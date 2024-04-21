/-
# Macros

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

import Lean

open Lean

syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quotation mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-
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

/-
This capability is obviously *very* powerful! It should not be used
lightly and without careful thinking since it can introduce weird
behaviour while writing code later on. The following example illustrates
this weird behaviour:
-/

#eval true LXOR true -- true, handled by new macro

def foo := true
#eval foo LXOR foo -- false, handled by old macro, after all the identifiers have a different name

/-
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

/-
As you can see, it figures out lot's of things on its own for us:
- the name of the syntax declaration
- the `macro` attribute registration
- the `throwUnsupported` wildcard

apart from this it just works like a function that is using pattern
matching syntax, we can in theory encode arbitrarily complex macro
functions on the right hand side.

If this is still not short enough for you, there is a next step using the
`macro` macro:
-/

macro l:term:10 " ⊕ " r:term:11 : term => `((!$l && $r) || ($l && !$r))

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

/-
As you can see, `macro` is quite close to `notation` already:
- it performed syntax declaration for us
- it automatically wrote a `macro_rules` style function to match on it

The are of course differences as well:
- `notation` is limited to the `term` syntax category
- `notation` cannot have arbitrary macro code on the right hand side

## `Syntax` Quotations
### The basics
So far we've handwaved the `` `(foo $bar) `` syntax to both create and
match on `Syntax` objects but it's time for a full explanation since
it will be essential to all non trivial things that are syntax related.

First things first we call the `` `() `` syntax a `Syntax` quotation.
When we plug variables into a syntax quotation like this: `` `($x) ``
we call the `$x` part an anti-quotation. When we insert `x` like this
it is required that `x` is of type `TSyntax x` where `x` is some `Name`
of a syntax category. The Lean compiler is actually smart enough to figure
the syntax categories that are allowed in this place out. Hence you might
sometimes see errors of the form:
```
application type mismatch
  x.raw
argument
  x
has type
  TSyntax `a : Type
but is expected to have type
  TSyntax `b : Type
```
If you are sure that your thing from the `a` syntax category can be
used as a `b` here you can declare a coercion of the form:
-/

instance : Coe (TSyntax `a) (TSyntax `b) where
  coe s := ⟨s.raw⟩

/-!
Which will allow Lean to perform the type cast automatically. If you
notice that your `a` can not be used in place of the `b` here congrats,
you just discovered a bug in your `Syntax` function. Similar to the Lean
compiler, you could also declare functions that are specific to certain
`TSyntax` variants. For example as we have seen in the syntax chapter
there exists the function:
-/
#check TSyntax.getNat -- TSyntax.getNat : TSyntax numLitKind → Nat
/-!
Which is guaranteed to not panic because we know that the `Syntax` that
the function is receiving is a numeric literal and can thus naturally
be converted to a `Nat`.

If we use the antiquotation syntax in pattern matching it will, as discussed
in the syntax chapter, give us a a variable `x` of type `` TSyntax y `` where
`y` is the `Name` of the syntax category that fits in the spot where we pattern matched.
If we wish to insert a literal `$x` into the `Syntax` for some reason,
for example macro creating macros, we can escape the anti quotation using: `` `($$x) ``.

If we want to specify the syntax kind we wish `x` to be interpreted as
we can make this explicit using: `` `($x:term) `` where `term` can be
replaced with any other valid syntax category (e.g. `command`) or parser
(e.g. `ident`).

So far this is only a more formal explanation of the intuitive things
we've already seen in the syntax chapter and up to now in this chapter,
next we'll discuss some more advanced anti-quotations.

### Advanced anti-quotations
For convenience we can also use anti-quotations in a way similar to
format strings: `` `($(mkIdent `c)) `` is the same as: `` let x := mkIdent `c; `($x) ``.

Furthermore there are sometimes situations in which we are not working
with basic `Syntax` but `Syntax` wrapped in more complex datastructures,
most notably `Array (TSyntax c)` or `TSepArray c s`. Where `TSepArray c s`, is a
`Syntax` specific type, it is what we get if we pattern match on some
`Syntax` that users a separator `s` to separate things from the category `c`.
For example if we match using: `$xs,*`, `xs` will have type `TSepArray c ","`,.
With the special case of matching on no specific separator (i.e. whitespace):
`$xs*` in which we will receive an `Array (TSyntax c)`.

If we are dealing with `xs : Array (TSyntax c)` and want to insert it into
a quotation we have two main ways to achieve this:
1. Insert it using a separator, most commonly `,`: `` `($xs,*) ``.
  This is also the way to insert a `TSepArray c ",""`
2. Insert it point blank without a separator (TODO): `` `() ``

For example:
-/

-- syntactically cut away the first element of a tuple if possible
syntax "cut_tuple " "(" term ", " term,+ ")" : term

macro_rules
  -- cutting away one element of a pair isn't possible, it would not result in a tuple
  | `(cut_tuple ($x, $y)) => `(($x, $y))
  | `(cut_tuple ($x, $y, $xs,*)) => `(($y, $xs,*))

#check cut_tuple (1, 2) -- (1, 2) : Nat × Nat
#check cut_tuple (1, 2, 3) -- (2, 3) : Nat × Nat

/-!
The last thing for this section will be so called "anti-quotation splices".
There are two kinds of anti quotation splices, first the so called optional
ones. For example we might declare a syntax with an optional argument,
say our own `let` (in real projects this would most likely be a `let`
in some functional language we are writing a theory about):
-/

syntax "mylet " ident (" : " term)? " := " term " in " term : term

/-!
There is this optional `(" : " term)?` argument involved which can let
the user define the type of the term to the left of it. With the methods
we know so far we'd have to write two `macro_rules` now, one for the case
with, one for the case without the optional argument. However the rest
of the syntactic translation works exactly the same with and without
the optional argument so what we can do using a splice here is to essentially
define both cases at once:
-/

macro_rules
  | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

/-!
The `$[...]?` part is the splice here, it basically says "if this part of
the syntax isn't there, just ignore the parts on the right hand side that
involve anti quotation variables involved here". So now we can run
this syntax both with and without type ascription:
-/

#eval mylet x := 5 in x - 10 -- 0, due to subtraction behaviour of `Nat`
#eval mylet x : Int := 5 in x - 10 -- -5, after all it is an `Int` now

/-!
The second and last splice might remind readers of list comprehension
as seen for example in Python. We will demonstrate it using an implementation
of `map` as a macro:
-/

-- run the function given at the end for each element of the list
syntax "foreach " "[" term,* "]" term : term

macro_rules
  | `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])

#eval foreach [1,2,3,4] (Nat.add 2) -- [3, 4, 5, 6]

/-!
In this case the `$[...],*` part is the splice. On the match side it tries
to match the pattern we define inside of it repetitively (given the separator
we tell it to). However unlike regular separator matching it does not
give us an `Array` or `SepArray`, instead it allows us to write another
splice on the right hand side that gets evaluated for each time the
pattern we specified matched, with the specific values from the match
per iteration.
-/

/-!
## Hygiene issues and how to solve them
If you are familiar with macro systems in other languages like C you
probably know about so called macro hygiene issues already.
A hygiene issue is when a macro introduces an identifier that collides with an
identifier from some syntax that it is including. For example:
-/

-- Applying this macro produces a function that binds a new identifier `x`.
macro "const" e:term : term => `(fun x => $e)

-- But `x` can also be defined by a user
def x : Nat := 42

-- Which `x` should be used by the compiler in place of `$e`?
#eval (const x) 10 -- 42

/-
Given the fact that macros perform only syntactic translations one might
expect the above `eval` to return 10 instead of 42: after all, the resulting
syntax should be `(fun x => x) 10`. While this was of course not the intention
of the author, this is what would happen in more primitive macro systems like
the one of C. So how does Lean avoid these hygiene issues? You can read
about this in detail in the excellent [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
paper which discusses the idea and implementation in Lean in detail.
We will merely give an overview of the topic, since the details are not
that interesting for practical uses. The idea described in Beyond Notations
comes down to a concept called "macro scopes". Whenever a new macro
is invoked, a new macro scope (basically a unique number) is added to
a list of all the macro scopes that are active right now. When the current
macro introduces a new identifier what is actually getting added is an
identifier of the form:
```
<actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
```
For example, if the module name is `Init.Data.List.Basic`, the name is
`foo.bla`, and macros scopes are [2, 5] we get:
```
foo.bla._@.Init.Data.List.Basic._hyg.2.5
```
Since macro scopes are unique numbers the list of macro scopes appended in the end
of the name will always be unique across all macro invocations, hence macro hygiene
issues like the ones above are not possible.

If you are wondering why there is more than just the macro scopes to this
name generation, that is because we may have to combine scopes from different files/modules.
The main module being processed is always the right most one.
This situation may happen when we execute a macro generated in a file
imported in the current file.
```
foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
```
The delimiter `_hyg` at the end is used just to improve performance of
the function `Lean.Name.hasMacroScopes` -- the format could also work without it.

This was a lot of technical details. You do not have to understand them
in order to use macros, if you want you can just keep in mind that Lean
will not allow name clashes like the one in the `const` example.

Note that this extends to *all* names that are introduced using syntax
quotations, that is if you write a macro that produces:
`` `(def foo := 1) ``, the user will not be able to access `foo`
because the name will subject to hygiene. Luckily there is a way to
circumvent this. You can use `mkIdent` to generate a raw identifier,
for example: `` `(def $(mkIdent `foo) := 1) ``. In this case it won't
be subject to hygiene and accessible to the user.

## `MonadQuotation` and `MonadRef`
Based on this description of the hygiene mechanism one interesting
question pops up, how do we know what the current list of macro scopes
actually is? After all in the macro functions that were defined above
there is never any explicit passing around of the scopes happening.
As is quite common in functional programming, as soon as we start
having some additional state that we need to bookkeep (like the macro scopes)
this is done with a monad, this is the case here as well with a slight twist.

Instead of implementing this for only a single monad `MacroM` the general
concept of keeping track of macro scopes in monadic way is abstracted
away using a type class called `MonadQuotation`. This allows any other
monad to also easily provide this hygienic `Syntax` creation mechanism
by simply implementing this type class.

This is also the reason that while we are able to use pattern matching on syntax
with `` `(syntax) `` we cannot just create `Syntax` with the same
syntax in pure functions: there is no `Monad` implementing `MonadQuotation`
involved in order to keep track of the macro scopes.

Now let's take a brief look at the `MonadQuotation` type class:
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

/-
Since `MonadQuotation` is based on `MonadRef`, let's take a look at `MonadRef`
first. The idea here is quite simple: `MonadRef` is meant to be seen as an extension
to the `Monad` typeclass which
- gives us a reference to a `Syntax` value with `getRef`
- can evaluate a certain monadic action `m α` with a new reference to a `Syntax`
  using `withRef`

On it's own `MonadRef` isn't exactly interesting, but once it is combined with
`MonadQuotation` it makes sense.

As you can see `MonadQuotation` extends `MonadRef` and adds 3 new functions:
- `getCurrMacroScope` which obtains the latest `MacroScope` that was created
- `getMainModule` which (obviously) obtains the name of the main module,
  both of these are used to create these hygienic identifiers explained above
- `withFreshMacroScope` which will compute the next macro scope and run
  some computation `m α` that performs syntax quotation with this new
  macro scope in order to avoid name clashes. While this is mostly meant
  to be used internally whenever a new macro invocation happens, it can sometimes
  make sense to use this in our own macros, for example when we are generating
  some syntax block repeatedly and want to avoid name clashes.

How `MonadRef` comes into play here is that Lean requires a way to indicate
errors at certain positions to the user. One thing that wasn't introduced
in the `Syntax` chapter is that values of type `Syntax` actually carry their
position in the file around as well. When an error is detected, it is usually
bound to a `Syntax` value which tells Lean where to indicate the error in the file.
What Lean will do when using `withFreshMacroScope` is to apply the position of
the result of `getRef` to each introduced symbol, which then results in better
error positions than not applying any position.

To see error positioning in action, we can write a little macro that makes use of it:
-/

syntax "error_position" ident : term

macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- the `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")

#check_failure error_position all -- the error is indicated at `error_position all`
#check_failure error_position first -- the error is only indicated at `error_position`

/-
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

/-! Again feel free to play around with it. If you want to build more complex
things, like expressions with variables, maybe consider building an inductive type
using macros instead. Once you got your arithmetic expression term
as an inductive, you could then write a function that takes some form of
variable assignment and evaluates the given expression for this
assignment. You could also try to embed arbitrary `term`s into your
arith language using some special syntax or whatever else comes to your mind.
-/

/-!
## More elaborate examples
### Binders 2.0
As promised in the syntax chapter here is Binders 2.0. We'll start by
reintroducing our theory of sets:
-/
def Set (α : Type u) := α → Prop
def Set.mem (x : α) (X : Set α) : Prop := X x

-- Integrate into the already existing typeclass for membership notation
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

-- the basic "all elements such that" function for the notation
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
The goal for this section will be to allow for both `{x : X | p x}`
and `{x ∈ X, p x}` notations. In principle there are two ways to do this:
1. Define a syntax and macro for each way to bind a variable we might think of
2. Define a syntax category of binders that we could reuse across other
   binder constructs such as `Σ` or `Π` as well and implement macros for
   the `{ | }` case

In this section we will use approach 2 because it is more easily reusable.
-/

declare_syntax_cat binder_construct
syntax "{" binder_construct "|" term "}" : term

/-!
Now let's define the two binders constructs we are interested in:
-/
syntax ident " : " term : binder_construct
syntax ident " ∈ " term : binder_construct

/-!
And finally the macros to expand our syntax:
-/

macro_rules
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

-- Old examples with better syntax:
#check { x : Nat | x ≤ 1 } -- setOf fun x => x ≤ 1 : Set Nat

example : 1 ∈ { y : Nat | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { y : Nat | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

-- New examples:
def oneSet : Set Nat := λ x => x = 1
#check { x ∈ oneSet | 10 ≤ x } -- setOf fun x => x ∈ oneSet ∧ 10 ≤ x : Set Nat

example : ∀ x, ¬(x ∈ { y ∈ oneSet | y ≠ 1 }) := by
  intro x h
  -- h : x ∈ setOf fun y => y ∈ oneSet ∧ y ≠ 1
  -- ⊢ False
  cases h
  -- : x ∈ oneSet
  -- : x ≠ 1
  contradiction


/-!
## Reading further
If you want to know more about macros you can read:
- the API docs: TODO link
- the source code: the lower parts of [Init.Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)
  as you can see they are declared quite early in Lean because of their importance
  to building up syntax
- the aforementioned [Beyond Notations](https://lmcs.episciences.org/9362/pdf) paper
-/
