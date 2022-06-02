import Lean

/-!
# Introduction

## What's the goal of this book?

This book aims to build up enough knowledge about metaprogramming in Lean 4 so
you can be comfortable enough to start building your own meta helpers.

We by no means intend to provide an exhaustive exploration/explanation of the
entire Lean 4 metaprogramming API. We also don't cover the topic of monadic
programming in Lean 4. However, the examples provided will be simple enough for
you to follow and comprehend without a super deep understanding of monadic
programming.

## What does it mean to be in meta?

When we write code in most programming languages such as Python, C, Java or
Scala, we usually have to stick to a pre-defined syntax otherwise the compiler
or the interpreter won't be able to figure out what we're trying to say. In
Lean, that would be defining an inductive type, implementing a function, proving
a theorem etc. The compiler, then, has to parse the code, build an abstract
syntax tree and elaborate its syntax nodes into terms that can be processed by
the language kernel. We say that such activities performed by the compiler are
done in the __meta-level__, which will be studied throughout the book. And we
also say that the common usage of the language syntax is done in the
__object-level__.

In most systems, the meta-level activities are done in a different language to
the one that we use to write code. In Isabelle, the meta-level language is ML
and Scala. In Coq, it's OCaml. In Agda it's Haskell. In Lean 4, the meta code is
mostly written in Lean itself, with a few components written in C++.

One cool thing about Lean, though, is that it allows us to define custom syntax
nodes and to implement our own meta-level routines to elaborate those in the
very same development environment that we use to perform object-level
activities. So for example, one can write their own notation to instantiate a
term of a certain type and use it right away, on the same file! This concept is
generally called
[__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). We can
say that, in Lean, the meta-level is _reflected_ to the object-level.

Since the objects defined in the meta-level are not the ones we're most
interested in proving theorems about, it can sometimes be overly tedious to
prove that they are type correct. For example, we don't care about proving that
a recursive function to traverse an expression is well founded. Thus, we can
use the `partial` keyword if we're convinced that our function terminates. In
the worst case scenario, our function gets stuck in a loop but the kernel is
not reached/affected.

Let's see some example use cases of metaprogramming in Lean.

## Metaprogramming examples

The following examples are meant for mere illustration. Don't worry if you don't
understand the details for now.

### Building a command

Suppose we want to build a helper command `#assertType` which tells whether a
given term is of a certain type. The usage will be:

`#assertType <term> : <type>`
-/

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean.Elab Command Term in
  liftTermElabM `assertTypeCmd
    try
      let tp ← elabType typeStx
      let tm ← elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

#assertType 5  : Nat -- success
#assertType [] : Nat -- failure

/-! We started by using `elab` to define a `command` syntax, which, when parsed
by the compiler, will trigger the incoming computation.

At this point, the code should be running in the `CommandElabM` monad. We then
use `liftTermElabM` to access the `TermElabM` monad, which allows us to use
`elabType` and `elabTermEnsuringType` in order to build expressions out of the
syntax nodes `typeStx` and `termStx`.

First we elaborate the expected type `tp : Expr` and then we use it to elaborate
the term `tm : Expr`, which should have the type `tp` otherwise an error will be
thrown.

We also add `synthesizeSyntheticMVarsNoPostponing`, which forces Lean to
elaborate metavariables right away. Without that line, `#assertType 5  : ?_`
would result in `success`.

If no error is thrown until now then the elaboration succeeded and we can use
`logInfo` to output "success". If, instead, some error is caught, then we use
`throwError` with the appropriate message.

### Building a DSL and a syntax for it

Let's parse a classic grammar, the grammar of arithmetic expressions with
addition, multiplication, naturals, and variables.  We'll define an AST, and use
operators `+` and `*` to denote building an arithmetic AST. Here's the AST that
we will be parsing:
-/

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

/-! Now we declare a syntax category to describe the grammar that we will be
parsing. Notice that we control the precedence of `+` and `*` by writing
`syntax:75` for multiplication indicating that multiplication binds tighter than
addition (the higher the number, the tighter the binding). This allows us to
declare _precedence_ when defining new syntax.
-/

declare_syntax_cat arith
syntax num                  : arith -- nat for Arith.nat
syntax str                  : arith -- strings for Arith.var
syntax arith " + " arith    : arith -- Arith.add
syntax:75 arith " * " arith : arith -- Arith.mul
syntax " ( " arith " ) "    : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
-- Arith.mul (Arith.symbol "x") (Arith.symbol "y")

#check ⟪ "x" + "y" ⟫
-- Arith.add (Arith.symbol "x") (Arith.symbol "y") 

#check ⟪ "x" + 20 ⟫
-- Arith.add (Arith.symbol "x") (Arith.int 20)

#check ⟪ "x" + "y" * "z" ⟫ -- precedence
-- Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))

#check ⟪ "x" * "y" + "z" ⟫ -- precedence
-- Arith.add (Arith.mul (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

#check ⟪ ("x" + "y") * "z" ⟫ -- brackets
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

/-!
### Writing our own tactic

Let's create a tactic that adds a new hypothesis to the context with a given
name and postpones the need for its proof to the very end. It's going to be
called `suppose` and is used like this:

`suppose <name> : <type>`
-/

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  withMVarContext mvarId do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← intro1P $ ← assert mvarId n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_comm`

/-! We start by storing the main goal in `mvarId` and using it as a parameter of
`withMVarContext` to make sure that our elaborations will work with types that
depend on other variables in the context.

This time we're using `mkFreshExprMVar` to create a metavariable expression for
the proof of `t`, which we can introduce to the context using `intro1P` and
`assert`.

To require the proof of the new hypothesis as a goal, we call `replaceMainGoal`
passing a list with `p.mvarId!` in the head. And then we can use the
`rotate_left` tactic to move the recently added top goal to the bottom.
-/


/-
## Printing Messages and Formatting Strings

As you saw, we used `logInfo "..."` above to get Lean to print out
information to the user.  In the examples above, we only printed a
string of characters.  However, in case we want to print some actual
expressions, then it can be useful to format them for easier reading.
-/
elab "#mylog " termStx:term " : " typeStx:term : command =>
  open Lean.Elab Command Term in
  liftTermElabM `assertTypeCmd
    try
      let tp ← elabType typeStx
      let tm ← elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo   "no options:\n'{tm}' has type '{tp}'\n"  -- bare printing of a string
      logInfo   "no options:\n'{termStx}' has type '{typeStx}'\n"  -- bare printing of a string
      logInfo s!"s! option:\n'{tm}' has type '{tp}'\n"  -- some processing before printing
      logInfo s!"s! option, terms:\n'{termStx}' has type '{typeStx}'\n"  -- some processing before printing
      logInfo m!"m! option:\n'{tm}' has type '{tp}'\n"  -- more processing before printing
      logInfo m!"m! option, terms:\n'{termStx}' has type '{typeStx}'\n"  -- more processing before printing
    catch | _ => throwError "failure"

#mylog -1 : Int
--  no options:
--  '{tm}' has type '{tp}'

--  no options:
--  '{termStx}' has type '{typeStx}'

--  s! option:
--  'Neg.neg.{?_uniq.7958} ?_uniq.7959 ?_uniq.7960 (OfNat.ofNat.{0} ?_uniq.7962 1 ?_uniq.7963)' has type 'Int'

--  s! option, terms:
--  '(«term-_» "-" (num "1"))' has type '`Int'

--  m! option:
--  '-1' has type 'Int'

--  m! option, terms:
--  '-1' has type 'Int'

/-
Go ahead and experiment with "wilder" examples, for instance
```lean
#mylog 1+1 : _
#mylog List.replicate 5 (List.range 8) : List (List Nat)
#mylog ["I","♥","28"] : List String
```

Besides `logInfo`, that is intended for producing "permanent" messages,
Lean also has a "debug trace" command, `dbg_trace`.  This command is
similar to `logInfo`.  Below is a quick comparison, where we define a
tactic: tactics appear later, we use them now simply to highlight some
differences between `logInfo` and `dbg_trace`.
-/

elab "traces" : tactic => do
  let array := List.replicate 5 (List.range 8)
  Lean.Elab.logInfo "logInfo nothing:\n{array}"
  Lean.Elab.logInfo s!"logInfo with s:\n{array}"
  Lean.Elab.logInfo f!"logInfo with f:\n{array}"
  Lean.Elab.logInfo m!"logInfo with m:\n{array}"
  dbg_trace f!"debug with f:\n{array}"
  dbg_trace "debug neither f nor s:\n{array}"

example : true :=
--  debug with f:
--  [[0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7]]
--  debug neither f nor s:
--  [[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]]
by traces
--  logInfo nothing:
--  {array}

--  logInfo with s:
--  [[0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]]

--  logInfo with f:
--  [[0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7]]

--  logInfo with m:
--  [[0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7],
--   [0, 1, 2, 3, 4, 5, 6, 7]]
   trivial

/-
As you can see, `dbg_trace` is displayed earlier than `logInfo`: it is printed
at `example` rather than at the actual tactic `traces`.

`dbg_trace <arg>` prints a slightly formatted version of `<arg>`.
That is, `dbg_trace "..."` gets macro expanded to `dbg_trace s!"..."`.
Thus, using the `s!` option on a string or using nothing results in the same output,
when the string is passed to `dbg_trace`.

There are in fact three options for formatting strings,
namely `f!"..."`, `s!"..."` and `m!"..."`.

* `f!"..."` interprets `...` using `Std.ToFormat`.  It outputs a `Std.Format`.
* `s!"..."` interprets `...` using `ToString`.  It outputs a `String`.
* `m!"..."` interprets `...` using `Lean.ToMessageData`.  It outputs a `Lean.MessageData`.

If the argument `<arg>` of `dbg_trace` is already a `String`, then `dbg_trace` prints it.
If the argument `<arg>` of `dbg_trace` is not a `String`, then `dbg_trace` prints
`toString <arg>` (or fails, if `toString` is not defined on `<arg>`).
Since `m!` produces `MessageData` and there is no `ToString` on `MessageData`,
the `m!` formatting option is not available for `dbg_trace`.

`dbg_trace f!"..."`, which gets converted to `dbg_trace toString f!"..."`,
may produce different outputs and can be easier to read.  We saw an example of this
above, with the formatting of
```lean
[[0, 1, 2, 3, 4, 5, 6, 7],
 [0, 1, 2, 3, 4, 5, 6, 7],
 [0, 1, 2, 3, 4, 5, 6, 7],
 [0, 1, 2, 3, 4, 5, 6, 7],
 [0, 1, 2, 3, 4, 5, 6, 7]]
```
-/
