import Lean
open Lean
/-! # Macros
## What is a macro
Macros in Lean are `Syntax → MacroM Syntax` functions. `MacroM` is the macro
monad which allows macros to have some static guarantees we will discuss in the
next section, you can mostly ignore it for now.

Macros are registered as handlers for a specific syntax declaration using the
`macro` attribute. The compiler will take care of applying these function
to the syntax for us before performing actual analysis of the input. This
means that the only thing we have to do is declare our syntax with a specific
name and bind a function of type `Lean.Macro` to it. Let's try to reproduce
the `LXOR` notation from the `Syntax` chapter:
-/

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quoting mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-!
That was quite easy! The `Macro.throwUnsupported` function can be used by a macro
to indicate that "it doesn't feel responsible for this syntax". In this case
it's merely used to fill a wildcard pattern that should never be reached anyways.

However we can in fact register multiple macros for the same syntax this way
if we desire, they will be tried one after another (the later registered ones have 
higher priority)  -- is "higher" correct?
until one throws either a real error using `Macro.throwError` or succeeds, that
is it does not `Macro.throwUnsupported`. Let's see this in action:
-/

@[macro lxor] def lxorImpl2 : Macro
  -- special case that changes behaviour of the case where the left and
  -- right hand side are these specific identifiers
  | `(true LXOR true) => `(true)
  | _ => Macro.throwUnsupported

#eval true LXOR true -- true, handled by new macro
#eval true LXOR false -- false, still handled by the old

/-!
This capability is obviously *very* powerful! It should not be used
lightly and without careful thinking since it can introduce weird
behaviour while writing code later on. The following example illustrates
this weird behaviour:
-/

#eval true LXOR true -- true, handled by new macro

def foo := true
#eval foo LXOR foo -- false, handled by old macro, after all the identifiers have a different name

/-!
Without knowing exactly how this macro is implemented this behaviour
will be very confusing to whoever might be debugging an issue based on this.
The rule of thumb for when to use a macro vs. other mechanisms like
elaboration is that as soon as you are building real logic like in the 2nd
macro above, it should most likely not be a macro but an elaborator
(explained in the elaboration chapter). This means ideally we want to
use macros for simple syntax to syntax translations, that a human could
easily write out themselves as well but is too lazy to.

## Simplifying macro declaration
Now that we know the basics of what a macro is and how to register it
we can take a look at slightly more automated ways to do this (in fact
all of the ways about to be presented are implemented as macros themselves).

First things first there is `macro_rules` which basically desugars to
functions like the ones we wrote above, for example:
-/

syntax:10 term:10 " RXOR " term:11 : term

macro_rules
  | `($l:term RXOR $r:term) => `($l && !$r)

/-!
As you can see, it figures out lot's of things on it's own for us:
- the name of the syntax declaration
- the `macro` attribute registration
- the `throwUnsupported` wildcard

apart from this it just works like a function that is using pattern
matching syntax, we can in theory encode arbitrarily complex macro
functions on the right hand side.

If this is still not short enough for you there is a next step using the
`macro` macro:
-/

macro l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

/-!
As you can see `macro` is quite close to `notation` already:
- it performed syntax declaration for us
- automatically wrote a `macro_rules` style function to match on it

The are of course differences as well:
- `notation` is limited to the `term` syntax category
- `notation` can not have arbitrary macro code on the right hand side

## Hygiene issues and how to solve them
If you are familiar with macro systems in other languages like C you
probably know about so called macro hygiene issues already. A hygiene
issue is, when a macro introduced an identifier that collides with an
identifier from some syntax that it is including, for example:
-/

macro "const" e:term : term => `(fun x => $e)

def x : Nat := 42

#eval (const x) 10 -- 42

/-!
Given the fact that macros perform only syntactic translation one might
expect the above eval to return 10 instead of 42, after all the resulting
syntax should be `(fun x => x) 10`. While this was of course not the intention
of the author this is what would happen in more primitive macro systems like
the one of C. So how does Lean avoid these hygiene issues? You can read
about this in detail in the excellent [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
paper which discusses the idea and implementation in Lean in detail,
we will merely give an overview of the topic since the details are not
that interesting to practical use. The idea described in beyond notations
comes down to a concept called "macro scopes". Whenever a new macro
is invoked a new macro scope (basically a unique number) is added to
a list of all the macro scopes that are active right now. When the current
macro introduces a new identifier what is actually getting added is an identifier of
the form:
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
For example if the module name is `Init.Data.List.Basic`, and name is `foo.bla`,
and macros copes are [2, 5] we get:
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```
Since macro scopes are unique numbers the list of macro scopes appended in the end
of the name will always be unique across all macro invocations, hence macro hygience
issues like the ones above are not possible.

If you are wondering why there is more than just the macro scopes to this
name generation, that is because we may have to combine scopes from different files/modules.
The main modules being processed is always the right most one.
This situation may happen when we execute a macro generated in
an imported file in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```
The delimiter `_hyg` in the end is used just to improve performance of
the function `Lean.Name.hasMacroScopes`, the format could also work without it.

This was a lot of technical details, you do not have to understand them
in order to use macros, if you want you can just keep in mind that Lean
will not allow name clashes like the one in the `const` example.

## `MonadQuotation` and `MonadRef`
This macro hygiene mechanism is the reason that while we are able to use pattern
matching on syntax with `` `(syntax) `` we cannot just create `Syntax` with the same
syntax in pure functions because someone has to keep track of macro scopes for us.
In this case this is done by the `MacroM` monad but can be done by any monad that
implements `Lean.MonadQuotation` so it's worth to take a brief look at it:
-/

namespace Playground

class MonadRef (m : Type → Type) where
  getRef      : m Syntax
  withRef {α} : Syntax → m α → m α

class MonadQuotation (m : Type → Type) extends MonadRef m where
  getCurrMacroScope : m MacroScope
  getMainModule     : m Name
  withFreshMacroScope {α : Type} : m α → m α

end Playground

/-!
Since `MonadQuotation` is based on `MonadRef` let's take a look at it
first. The idea here is quite simple, it's meant to be seen as an extension
to the `Monad` typeclass which can give us a reference to a `Syntax` value
with `getRef` and evaluate a function of type `Syntax → m α` to `m α` by
the return value of `getRef` to this `Syntax` parameter and evaluting the
`m α` parameter with that new state.

On it's own `MonadRef` isn't exactly interesting but once combined with
`MonadQuotation` it makes sense.

As you can see `MonadQuotation` extends `MonadRef` and adds 3 new functions:
- `getCurrMacroScope` which obtains the latest `MacroScope` that was created
- `getMainModule` which (obviously) obtains the name of the main module,
  both of these are used to create these hygienic identifiers explained above
- `withFreshMacroScope` which will compute the next macro scope and run
  some computation `m α` that performs syntax quotation with this new
  macro scope in order to avoid name clashes. While this is mostly meant
  to be used internally whenver a new macro invocation happens it can sometimes
  make sense to use this in our own macros, for example when we are generating
  some syntax block repeatedly and want to avoid name clashes.

How `MonadRef` comes into play here is that Lean requires a way to indicate
errors at certain positions to the user. One thing that wasn't introduced
in the `Syntax` chapter is that values of type `Syntax` actually carry their
position in the file around as well, when an error is detected it is usually
bound to a `Syntax` value which tells Lean where to indicate the error in the file.
What Lean will do when using `withFreshMacroScope` apply the position of
the result of `getRef` to each introduced symbol, which then results in better
error positions than not applying any position.

To see error positioning in action we can write a little macro that makes use of it:
-/

syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#eval error_position all -- the error is indicated at `error_position all`
#eval error_position first -- the error is only indicated at `error_position`

/-!
Obviously controlling the positions of errors in this way is quite important
for a good user experience.

## Mini project
As a final mini project for this section we will re-build the arithmetic
DSL from the syntax chapter in a slightly more advanced way, using a macro
this time so we can actually fully integrate it into the Lean syntax.
-/
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith
syntax "[Arith|" arith "]" : term

macro_rules
  | `([Arith| $x:num]) => `($x)
  | `([Arith| $x:arith + $y:arith]) => `([Arith| $x] + [Arith| $y]) -- recursive macros are possible
  | `([Arith| $x:arith - $y:arith]) => `([Arith| $x] - [Arith| $y])
  | `([Arith| ($x:arith)]) => `([Arith| $x])

#eval [Arith| (12 + 3) - 4] -- 11

/-!
Again feel free to play around with it, if you want to build more complex
things like expressions with variables maybe consider building an inductive type
using the macros instead. Once you got your arithmetic expression term
as an inductive you could then write a function  that takes some form of
variable assignment and evaluates the given expression for this
assignment. You could also try to embed arbitrary `term`s into your
arith language using some special syntax or whatever else comes to your mind.

## Reading further
If you want to know more about macros you can read:
- the API docs: TODO link
- the source code: the lower parts of [Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)
  as you can see they are declared quite early in Lean because of their importance
  of to building up syntax
- the aforementioned [Beyond Notations](https://lmcs.episciences.org/9362/pdf) paper
-/
