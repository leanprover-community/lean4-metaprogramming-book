/-
# Elaboration

The elaborator is the component in charge of turning the user facing
`Syntax` into something with which the rest of the compiler can work.
Most of the time, this means translating `Syntax` into `Expr`s but
there are also other use cases such as `#check` or `#eval`. Hence the
elaborator is quite a large piece of code, it lives
[here](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab).

## Command elaboration
A command is the highest level of `Syntax`, a Lean file is made
up of a list of commands. The most commonly used commands are declarations,
for example:
- `def`
- `inductive`
- `structure`

but there are also other ones, most notably `#check`, `#eval` and friends.
All commands live in the `command` syntax category so in order to declare
custom commands, their syntax has to be registered in that category.

### Giving meaning to commands
The next step is giving some semantics to the syntax. With commands, this
is done by registering a so called command elaborator.

Command elaborators have type `CommandElab` which is an alias for:
`Syntax → CommandElabM Unit`. What they do, is take the `Syntax` that
represents whatever the user wants to call the command and produce some
sort of side effect on the `CommandElabM` monad, after all the return
value is always `Unit`. The `CommandElabM` monad has 4 main kinds of
side effects:
1. Logging messages to the user via the `Monad` extensions
   `MonadLog` and `AddMessageContext`, like `#check`. This is done via
   functions that can be found in `Lean.Elab.Log`, the most notable ones
   being: `logInfo`, `logWarning` and `logError`.
2. Interacting with the `Environment` via the `Monad` extension `MonadEnv`.
   This is the place where all of the relevant information for the compiler
   is stored, all known declarations, their types, doc-strings, values etc.
   The current environment can be obtained via `getEnv` and set via `setEnv`
   once it has been modified. Note that quite often wrappers around `setEnv`
   like `addDecl` are the correct way to add information to the `Environment`.
3. Performing `IO`, `CommandElabM` is capable of running any `IO` operation.
   For example reading from files and based on their contents perform
   declarations.
4. Throwing errors, since it can run any kind of `IO`, it is only natural
   that it can throw errors via `throwError`.

Furthermore there are a bunch of other `Monad` extensions that are supported
by `CommandElabM`:
- `MonadRef` and `MonadQuotation` for `Syntax` quotations like in macros
- `MonadOptions` to interact with the options framework
- `MonadTrace` for debug trace information
- TODO: There are a few others though I'm not sure whether they are relevant,
  see the instance in `Lean.Elab.Command`

### Command elaboration
Now that we understand the type of command elaborators let's take a brief
look at how the elaboration process actually works:
1. Check whether any macros can be applied to the current `Syntax`.
   If there is a macro that does apply and does not throw an error
   the resulting `Syntax` is recursively elaborated as a command again.
2. If no macro can be applied, we search for all `CommandElab`s that have been
   registered for the `SyntaxKind` of the `Syntax` we are elaborating,
   using the `command_elab` attribute.
3. All of these `CommandElab` are then tried in order until one of them does not throw an
   `unsupportedSyntaxException`, Lean's way of indicating that the elaborator
   "feels responsible"
   for this specific `Syntax` construct. Note that it can still throw a regular
   error to indicate to the user that something is wrong. If no responsible
   elaborator is found, then the command elaboration is aborted with an `unexpected syntax`
   error message.

As you can see the general idea behind the procedure is quite similar to ordinary macro expansion.

### Making our own
Now that we know both what a `CommandElab` is and how they are used, we can
start looking into writing our own. The steps for this, as we learned above, are:
1. Declaring the syntax
2. Declaring the elaborator
3. Registering the elaborator as responsible for the syntax via the `command_elab`
   attribute.

Let's see how this is done:
-/

import Lean

open Lean Elab Command Term Meta

syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1 -- Hello World

/-!
You might think that this is a little boiler-platey and it turns out the Lean
devs did as well so they added a macro for this!
-/
elab "#mycommand2" : command =>
  logInfo "Hello World"

#mycommand2 -- Hello World

/-!
Note that, due to the fact that command elaboration supports multiple
registered elaborators for the same syntax, we can in fact overload
syntax, if we want to.
-/
@[command_elab mycommand1]
def myNewImpl : CommandElab := fun stx => do
  logInfo "new!"

#mycommand1 -- new!

/-!
Furthermore it is also possible to only overload parts of syntax by
throwing an `unsupportedSyntaxException` in the cases we want the default
handler to deal with it or just letting the `elab` command handle it.
-/

/-
In the following example, we are not extending the original `#check` syntax,
but adding a new `SyntaxKind` for this specific syntax construct.
However, from the point of view of the user, the effect is basically the same.
-/
elab "#check" "mycheck" : command => do
  logInfo "Got ya!"

/-
This is actually extending the original `#check`
-/
@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax

#check mycheck -- Got ya!
#check "Hello" -- Specially elaborated string literal!: Hello : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

/-!
### Mini project
As a final mini project for this section let's build a command elaborator
that is actually useful. It will take a command and use the same mechanisms
as `elabCommand` (the entry point for command elaboration) to tell us
which macros or elaborators are relevant to the command we gave it.

We will not go through the effort of actually reimplementing `elabCommand` though
-/
elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab abbrev lolo := 12 -- Your syntax may be elaborated by: [Lean.Elab.Command.elabDeclaration]
#findCElab #check foo -- even our own syntax!: Your syntax may be elaborated by: [mySpecialCheck, Lean.Elab.Command.elabCheck]
#findCElab open Hi -- Your syntax may be elaborated by: [Lean.Elab.Command.elabOpen]
#findCElab namespace Foo -- Your syntax may be elaborated by: [Lean.Elab.Command.elabNamespace]
#findCElab #findCElab open Bar -- even itself!: Your syntax may be elaborated by: [«_aux_lean_elaboration___elabRules_command#findCElab__1»]

/-!
TODO: Maybe we should also add a mini project that demonstrates a
non # style command aka a declaration, although nothing comes to mind right now.
TODO:  Define a `conjecture` declaration, similar to `lemma/theorem`, except that
it is automatically sorried.  The `sorry` could be a custom one, to reflect that
the "conjecture" might be expected to be true.
-/

/-!
## Term elaboration
A term is a `Syntax` object that represents some sort of `Expr`.
Term elaborators are the ones that do the work for most of the code we write.
Most notably they elaborate all the values of things like definitions,
types (since these are also just `Expr`) etc.

All terms live in the `term` syntax category (which we have seen in action
in the macro chapter already). So, in order to declare custom terms, their
syntax needs to be registered in that category.

### Giving meaning to terms
As with command elaboration, the next step is giving some semantics to the syntax.
With terms, this is done by registering a so called term elaborator.

Term elaborators have type `TermElab` which is an alias for:
`Syntax → Option Expr → TermElabM Expr`. This type is already
quite different from command elaboration:
- As with command elaboration the `Syntax` is whatever the user used
  to create this term
- The `Option Expr` is the expected type of the term, since this cannot
  always be known it is only an `Option` argument
- Unlike command elaboration, term elaboration is not only executed
  because of its side effects -- the `TermElabM Expr` return value does
  actually contain something of interest, namely, the `Expr` that represents
  the `Syntax` object.

`TermElabM` is basically an upgrade of `CommandElabM` in every regard:
it supports all the capabilities we mentioned above, plus two more.
The first one is quite simple: On top of running `IO` code it is also
capable of running `MetaM` code, so `Expr`s can be constructed nicely.
The second one is very specific to the term elaboration loop.

### Term elaboration
The basic idea of term elaboration is the same as command elaboration:
expand macros and recurse or run term elaborators that have been registered
for the `Syntax` via the `term_elab` attribute (they might in turn run term elaboration)
until we are done. There is, however, one special action that a term elaborator
can do during its execution.

A term elaborator may throw `Except.postpone`. This indicates that
the term elaborator requires more
information to continue its work. In order to represent this missing information,
Lean uses so called synthetic metavariables. As you know from before, metavariables
are holes in `Expr`s that are waiting to be filled in. Synthetic metavariables are
different in that they have special methods that are used to solve them,
registered in `SyntheticMVarKind`. Right now, there are four of these:
- `typeClass`, the metavariable should be solved with typeclass synthesis
- `coe`, the metavariable should be solved via coercion (a special case of typeclass)
- `tactic`, the metavariable is a tactic term that should be solved by running a tactic
- `postponed`, the ones that are created at `Except.postpone`

Once such a synthetic metavariable is created, the next higher level term elaborator will continue.
At some point, execution of postponed metavariables will be resumed by the term elaborator,
in hopes that it can now complete its execution. We can try to see this in
action with the following example:
-/
#check set_option trace.Elab.postpone true in List.foldr .add 0 [1,2,3] -- [Elab.postpone] .add : ?m.5695 → ?m.5696 → ?m.5696

/-!
What happened here is that the elaborator for function applications started
at `List.foldr` which is a generic function so it created metavariables
for the implicit type parameters. Then, it attempted to elaborate the first argument `.add`.

In case you don't know how `.name` works, the basic idea is that quite
often (like in this case) Lean should be able to infer the output type (in this case `Nat`)
of a function (in this case `Nat.add`).  In such cases, the `.name` feature will then simply
search for a function named `name` in the namespace `Nat`. This is especially
useful when you want to use constructors of a type without referring to its
namespace or opening it, but can also be used like above.

Now back to our example, while Lean does at this point already know that `.add`
needs to have type: `?m1 → ?m2 → ?m2` (where `?x` is notation for a metavariable)
the elaborator for `.add` does need to know the actual value of `?m2` so the
term elaborator postpones execution (by internally creating a synthetic metavariable
in place of `.add`), the elaboration of the other two arguments then yields the fact that
`?m2` has to be `Nat` so once the `.add` elaborator is continued it can work with
this information to complete elaboration.

We can also easily provoke cases where this does not work out. For example:
-/

#check_failure set_option trace.Elab.postpone true in List.foldr .add
-- [Elab.postpone] .add : ?m.5808 → ?m.5809 → ?m.5809
-- invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  -- ?m.5808 → ?m.5809 → ?m.5809

/-!
In this case `.add` first postponed its execution, then got called again
but didn't have enough information to finish elaboration and thus failed.

### Making our own
Adding new term elaborators works basically the same way as adding new
command elaborators so we'll only take a very brief look:
-/

syntax (name := myterm1) "myterm 1" : term

def mytermValues := [1, 2]

@[term_elab myterm1]
def myTerm1Impl : TermElab := fun stx type? =>
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 0] -- `MetaM` code

#eval myterm 1 -- 1

-- Also works with `elab`
elab "myterm 2" : term => do
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 1] -- `MetaM` code

#eval myterm 2 -- 2

/-!
### Mini project
As a final mini project for this chapter we will recreate one of the most
commonly used Lean syntax sugars, the `⟨a,b,c⟩` notation as a short hand
for single constructor types:
-/

-- slightly different notation so no ambiguity happens
syntax (name := myanon) "⟨⟨" term,* "⟩⟩" : term

def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | _ => pure []

@[term_elab myanon]
def myanonImpl : TermElab := fun stx typ? => do
  -- Attempt to postpone execution if the type is not known or is a metavariable.
  -- Metavariables are used by things like the function elaborator to fill
  -- out the values of implicit parameters when they haven't gained enough
  -- information to figure them out yet.
  -- Term elaborators can only postpone execution once, so the elaborator
  -- doesn't end up in an infinite loop. Hence, we only try to postpone it,
  -- otherwise we may cause an error.
  tryPostponeIfNoneOrMVar typ?
  -- If we haven't found the type after postponing just error
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then
    throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  let stx ← `($(mkIdent ctor) $args*) -- syntax quotations
  elabTerm stx typ -- call term elaboration recursively

#check (⟨⟨1, sorry⟩⟩ : Fin 12) -- { val := 1, isLt := (_ : 1 < 12) } : Fin 12
#check_failure ⟨⟨1, sorry⟩⟩ -- expected type must be known
#check_failure (⟨⟨0⟩⟩ : Nat) -- type doesn't have exactly one constructor
#check_failure (⟨⟨⟩⟩ : Nat → Nat) -- type is not of the expected form: Nat -> Nat

/-!
As a final note, we can shorten the postponing act by using an additional
syntax sugar of the `elab` syntax instead:
-/

-- This `t` syntax will effectively perform the first two lines of `myanonImpl`
elab "⟨⟨" args:term,* "⟩⟩" : term <= t => do
  sorry


/-!

## Exercises

1. Consider the following code. Rewrite `syntax` + `@[term_elab hi]... : TermElab` combination using just `elab`.

    ```lean
    syntax (name := hi) term " ♥ " " ♥ "? " ♥ "? : term

    @[term_elab hi]
    def heartElab : TermElab := fun stx tp =>
      match stx with
        | `($l:term ♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)
        | `($l:term ♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
        | `($l:term ♥♥♥) => do
          let nExpr ← elabTermEnsuringType l (mkConst `Nat)
          return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
        | _ =>
          throwUnsupportedSyntax
    ```

2. Here is some syntax taken from a real mathlib command `alias`.

    ```
    syntax (name := our_alias) (docComment)? "our_alias " ident " ← " ident* : command
    ```

    We want `alias hi ← hello yes` to print out the identifiers after `←` - that is, "hello" and "yes".

    Please add these semantics:

    **a)** using `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

3. Here is some syntax taken from a real mathlib tactic `nth_rewrite`.

    ```lean
    open Parser.Tactic
    syntax (name := nthRewriteSeq) "nth_rewrite " (config)? num rwRuleSeq (ppSpace location)? : tactic
    ```

    We want `nth_rewrite 5 [←add_zero a] at h` to print out `"rewrite location!"` if the user provided location, and `"rewrite target!"` if the user didn't provide location.

    Please add these semantics:

    **a)** using `syntax` + `@[tactic nthRewrite] def elabNthRewrite : Lean.Elab.Tactic.Tactic`.
    **b)** using `syntax` + `elab_rules`.
    **c)** using `elab`.

-/
