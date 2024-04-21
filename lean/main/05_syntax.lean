/- # Syntax

This chapter is concerned with the means to declare and operate on syntax
in Lean. Since there are a multitude of ways to operate on it, we will
not go into great detail about this yet and postpone quite a bit of this to
later chapters.

## Declaring Syntax

### Declaration helpers

Some readers might be familiar with the `infix` or even the `notation`
commands, for those that are not here is a brief recap:
-/

import Lean

-- XOR, denoted \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/- As we can see the `infixl` command allows us to declare a notation for
a binary operation that is infix, meaning that the operator is in between
the operands (as opposed to e.g. before which would be done using the `prefix` command).
The `l` at the end of `infixl` means that the notation is left associative so `a ⊕ b ⊕ c`
gets parsed as `(a ⊕ b) ⊕ c` as opposed to `a ⊕ (b ⊕ c)` (which would be achieved by `infixr`).
On the right hand side, it expects a function that operates on these two parameters
and returns some value. The `notation` command, on the other hand, allows us some more
freedom: we can just "mention" the parameters right in the syntax definition
and operate on them on the right hand side. It gets even better though, we can
in theory create syntax with 0 up to as many parameters as we wish using the
`notation` command, it is hence also often referred to as "mixfix" notation.

The two unintuitive parts about these two are:
- The fact that we are leaving spaces around our operators: " ⊕ ", " LXOR ".
  This is so that, when Lean pretty prints our syntax later on, it also
  uses spaces around the operators, otherwise the syntax would just be presented
  as `l⊕r` as opposed to `l ⊕ r`.
- The `60` and `10` right after the respective commands -- these denote the operator
  precedence, meaning how strong they bind to their arguments, let's see this in action:
-/

#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

/-!
As we can see, the Lean interpreter analyzed the first term without parentheses
like the second instead of the third one. This is because the `⊕` notation
has higher precedence than `LXOR` (`60 > 10` after all) and is thus evaluated before it.
This is also how you might implement rules like `*` being evaluated before `+`.

Lastly at the `notation` example there are also these `:precedence` bindings
at the arguments: `l:10` and `r:11`. This conveys that the left argument must have
precedence at least 10 or greater, and the right argument must have precedence at 11
or greater. The way the arguments are assigned their respective precedence is by looking at
the precedence of the rule that was used to parse them. Consider for example
`a LXOR b LXOR c`. Theoretically speaking this could be parsed in two ways:
1. `(a LXOR b) LXOR c`
2. `a LXOR (b LXOR c)`

Since the arguments in parentheses are parsed by the `LXOR` rule with precedence
10 they will appear as arguments with precedence 10 to the outer `LXOR` rule:
1. `(a LXOR b):10 LXOR c`
2. `a LXOR (b LXOR c):10`

However if we check the definition of `LXOR`: `notation:10 l:10 " LXOR " r:11`
we can see that the right hand side argument requires a precedence of at least 11
or greater, thus the second parse is invalid and we remain with: `(a LXOR b) LXOR c`
assuming that:
- `a` has precedence 10 or higher
- `b` has precedence 11 or higher
- `c` has precedence 11 or higher

Thus `LXOR` is a left associative notation. Can you make it right associative?

NOTE: If parameters of a notation are not explicitly given a precedence they will implicitly be tagged with precedence 0.

As a last remark for this section: Lean will always attempt to obtain the longest
matching parse possible, this has three important implications.
First a very intuitive one, if we have a right associative operator `^`
and Lean sees something like `a ^ b ^ c`, it will first parse the `a ^ b`
and then attempt to keep parsing (as long as precedence allows it) until
it cannot continue anymore. Hence Lean will parse this expression as `a ^ (b ^ c)`
(as we would expect it to).

Secondly, if we have a notation where precedence does not allow to figure
out how the expression should be parenthesized, for example:
-/

notation:65 lhs:65 " ~ " rhs:65 => (lhs - rhs)

/-!
An expression like `a ~ b ~ c` will be parsed as `a ~ (b ~ c)` because
Lean attempts to find the longest parse possible. As a general rule of thumb:
If precedence is ambiguous Lean will default to right associativity.
-/

#eval 5 ~ 3 ~ 3 -- 5 because this is parsed as 5 - (3 - 3)

/-!
Lastly, if we define overlapping notation such as:
-/

-- define `a ~ b mod rel` to mean that a and b are equivalent with respect to some equivalence relation rel
notation:65 a:65 " ~ " b:65 " mod " rel:65 => rel a b

/-!
Lean will prefer this notation over parsing `a ~ b` as defined above and
then erroring because it doesn't know what to do with `mod` and the
relation argument:
-/

#check 0 ~ 0 mod Eq -- 0 = 0 : Prop

/-!
This is again because it is looking for the longest possible parser which
in this case involves also consuming `mod` and the relation argument.
-/

/-!
### Free form syntax declarations
With the above `infix` and `notation` commands, you can get quite far with
declaring ordinary mathematical syntax already. Lean does however allow you to
introduce arbitrarily complex syntax as well. This is done using two main commands
`syntax` and `declare_syntax_cat`. A `syntax` command allows you add a new
syntax rule to an already existing so-called "syntax category". The most common syntax
categories are:
- `term`, this category will be discussed in detail in the elaboration chapter,
  for now you can think of it as "the syntax of everything that has a value"
- `command`, this is the category for top-level commands like `#check`, `def` etc.
- TODO: ...

Let's see this in action:
-/

syntax "MyTerm" : term

/-!
We can now write `MyTerm` in place of things like `1 + 1` and it will be
*syntactically* valid, this does not mean the code will compile yet,
it just means that the Lean parser can understand it:
-/

#check_failure MyTerm
-- elaboration function for 'termMyTerm' has not been implemented
--   MyTerm

/-! Note: `#check_failure` command allows incorrectly typed terms to be indicated without error. -/

/-!
Implementing this so-called "elaboration function", which will actually
give meaning to this syntax in terms of Lean's fundamental `Expr` type,
is topic of the elaboration chapter.

The `notation` and `infix` commands are utilities that conveniently bundle syntax declaration
with macro definition (for more on macros, see the macro chapter),
where the contents left of the `=>` declare the syntax.
All the previously mentioned principles from `notation` and `infix` regarding precedence
fully apply to `syntax` as well.

We can, of course, also involve other syntax into our own declarations
in order to build up syntax trees. For example, we could try to build our
own little boolean expression language:
-/

namespace Playground2

-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check_failure ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

/-!
While this does work, it allows arbitrary terms to the left and right of our
`AND` and `OR` operation. If we want to write a mini language that only accepts
our boolean language on a syntax level we will have to declare our own
syntax category on top. This is done using the `declare_syntax_cat` command:
-/

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

/-!
Now that we are working in our own syntax category, we are completely
disconnected from the rest of the system. And these cannot be used in place of
terms anymore:

```lean
#check ⊥ AND ⊤ -- expected term
```
-/

/-!
In order to integrate our syntax category into the rest of the system we will
have to extend an already existing one with new syntax, in this case we
will re-embed it into the `term` category:
-/

syntax "[Bool|" boolean_expr "]" : term
#check_failure [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes

/-!
### Syntax combinators
In order to declare more complex syntax, it is often very desirable to have
some basic operations on syntax already built-in, these include:

- helper parsers without syntax categories (i.e. not extendable)
- alternatives
- repetitive parts
- optional parts

While all of these do have an encoding based on syntax categories, this
can make things quite ugly at times, so Lean provides an easier way to do all
of these.

In order to see all of these in action, we will briefly define a simple
binary expression syntax.
First things first, declaring named parsers that don't belong to a syntax
category is quite similar to ordinary `def`s:
-/

syntax binOne := "O"
syntax binZero := "Z"

/-!
These named parsers can be used in the same positions as syntax categories
from above, their only difference to them is, that they are not extensible.
That is, they are directly expanded within syntax declarations,
and we cannot define new patterns for them as we would with proper syntax categories.
There does also exist a number of built-in named parsers that are generally useful,
most notably:
- `str` for string literals
- `num` for number literals
- `ident` for identifiers
- ... TODO: better list or link to compiler docs

Next up we want to declare a parser that understands digits, a binary digit is
either 0 or 1 so we can write:
-/

syntax binDigit := binZero <|> binOne

/-!
Where the `<|>` operator implements the "accept the left or the right" behaviour.
We can also chain them to achieve parsers that accept arbitrarily many, arbitrarily complex
other ones. Now we will define the concept of a binary number, usually this would be written
as digits directly after each other but we will instead use comma separated ones to showcase
the repetition feature:
-/

-- the "+" denotes "one or many", in order to achieve "zero or many" use "*" instead
-- the "," denotes the separator between the `binDigit`s, if left out the default separator is a space
syntax binNumber := binDigit,+

/-!
Since we can just use named parsers in place of syntax categories, we can now easily
add this to the `term` category:

```lean
syntax "bin(" binNumber ")" : term
#check bin(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check bin() -- fails to parse because `binNumber` is "one or many": expected 'O' or 'Z'
```
-/

syntax binNumber' := binDigit,* -- note the *
syntax "emptyBin(" binNumber' ")" : term
#check_failure emptyBin() -- elaboration function hasn't been implemented but parsing passes

/-!
Note that nothing is limiting us to only using one syntax combinator per parser,
we could also have written all of this inline:
-/

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
#check_failure binCompact(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
As a final feature, let's add an optional string comment that explains the binary
literal being declared:
-/

-- The (...)? syntax means that the part in parentheses is optional
syntax "binDoc(" (str ";")? binNumber ")" : term
#check_failure binDoc(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check_failure binDoc("mycomment"; Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
## Operating on Syntax
As explained above, we will not go into detail in this chapter on how to teach
Lean about the meaning you want to give your syntax. We will, however, take a look
at how to write functions that operate on it. Like all things in Lean, syntax is
represented by the inductive type `Lean.Syntax`, on which we can operate. It does
contain quite some information, but most of what we are interested in, we can
condense in the following simplified view:
-/

namespace Playground2

inductive Syntax where
  | missing : Syntax
  | node (kind : Lean.SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Lean.Name -> Syntax

end Playground2

/-!
Lets go through the definition one constructor at a time:
- `missing` is used when there is something the Lean compiler cannot parse,
  it is what allows Lean to have a syntax error in one part of the file but
  recover from it and try to understand the rest of it. This also means we pretty
  much don't care about this constructor.
- `node` is, as the name suggests, a node in the syntax tree. It has a so called
  `kind : SyntaxNodeKind` where `SyntaxNodeKind` is just a `Lean.Name`. Basically,
  each of our `syntax` declarations receives an automatically generated `SyntaxNodeKind`
  (we can also explicitly specify the name with `syntax (name := foo) ... : cat`) so
  we can tell Lean "this function is responsible for processing this specific syntax construct".
  Furthermore, like all nodes in a tree, it has children, in this case in the form of
  an `Array Syntax`.
- `atom` represents (with the exception of one) every syntax object that is at the bottom of the
  hierarchy. For example, our operators ` ⊕ ` and ` LXOR ` from above will be represented as
  atoms.
- `ident` is the mentioned exception to this rule. The difference between `ident` and `atom`
  is also quite obvious: an identifier has a `Lean.Name` instead of a `String` that represents it.
  Why a `Lean.Name` is not just a `String` is related to a concept called macro hygiene
  that will be discussed in detail in the macro chapter. For now, you can consider them
  basically equivalent.

### Constructing new `Syntax`
Now that we know how syntax is represented in Lean, we could of course write programs that
generate all of these inductive trees by hand, which would be incredibly tedious and is something
we most definitely want to avoid. Luckily for us there is quite an extensive API hidden inside the
`Lean.Syntax` namespace we can explore:
-/

open Lean
#check Syntax -- Syntax. autocomplete

/-!
The interesting functions for creating `Syntax` are the `Syntax.mk*` ones that allow us to create
both very basic `Syntax` objects like `ident`s but also more complex ones like `Syntax.mkApp`
which we can use to create the `Syntax` object that would amount to applying the function
from the first argument to the argument list (all given as `Syntax`) in the second one.
Let's see a few examples:
-/

-- Name literals are written with this little ` in front of the name
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- is the syntax of `Nat.add 1 1`
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- is the syntax for `1 + 1`

-- note that the `«term_+_» is the auto-generated SyntaxNodeKind for the + syntax

/-
If you don't like this way of creating `Syntax` at all you are not alone.
However, there are a few things involved with the machinery of doing this in
a pretty and correct (the machinery is mostly about the correct part) way
which will be explained in the macro chapter.

### Matching on `Syntax`
Just like constructing `Syntax` is an important topic, especially
with macros, matching on syntax is equally (or in fact even more) interesting.
Luckily we don't have to match on the inductive type itself either: we can
instead use so-called "syntax patterns". They are quite simple, their syntax is just
`` `(the syntax I want to match on) ``. Let's see one in action:
-/

def isAdd11 : Syntax → Bool
  | `(Nat.add 1 1) => true
  | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false

/-!
The next level with matches is to capture variables from the input instead
of just matching on literals, this is done with a slightly fancier-looking syntax:
-/

def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

/-!
### Typed Syntax
Note that `x` and `y` in this example are of type `` TSyntax `term ``, not `Syntax`.
Even though we are pattern matching on `Syntax` which, as we can see in the constructors,
is purely composed of types that are not `TSyntax`, so what is going on?
Basically the `` `() `` Syntax is smart enough to figure out the most general
syntax category the syntax we are matching might be coming from (in this case `term`).
It will then use the typed syntax type `TSyntax` which is parameterized
by the `Name` of the syntax category it came from. This is not only more
convenient for the programmer to see what is going on, it also has other
benefits. For Example if we limit the syntax category to just `num`
in the next example Lean will allow us to call `getNat` on the resulting
`` TSyntax `num `` directly without pattern matching or the option to panic:
-/

-- Now we are also explicitly marking the function to operate on term syntax
def isLitAdd : TSyntax `term → Option Nat
  | `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
  | _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- none

/-!
If you want to access the `Syntax` behind a `TSyntax` you can do this using
`TSyntax.raw` although the coercion machinery should just work most of the time.
We will see some further benefits of the `TSyntax` system in the macro chapter.

One last important note about the matching on syntax: In this basic
form it only works on syntax from the `term` category. If you want to use
it to match on your own syntax categories you will have to use `` `(category| ...)``.

### Mini Project
As a final mini project for this chapter we will declare the syntax of a mini
arithmetic expression language and a function of type `Syntax → Nat` to evaluate
it. We will see more about some of the concepts presented below in future
chapters.
-/

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

-- You can ignore Elab.TermElabM, what is important for us is that it allows
-- us to use the ``(arith| (12 + 3) - 4)` notation to construct `Syntax`
-- instead of only being able to match on it like this.
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  pure (denoteArith stx)

#eval test -- 11

/-!
Feel free to play around with this example and extend it in whatever way
you want to. The next chapters will mostly be about functions that operate
on `Syntax` in some way.
-/

/-!
## More elaborate examples
### Using type classes for notations
We can use type classes in order to add notation that is extensible via
the type instead of the syntax system, this is for example how `+`
using the typeclasses `HAdd` and `Add` and other common operators in
Lean are generically defined.

For example, we might want to have a generic notation for subset notation.
The first thing we have to do is define a type class that captures
the function we want to build notation for.
-/

class Subset (α : Type u) where
  subset : α → α → Prop

/-!
The second step is to define the notation, what we can do here is simply
turn every instance of a `⊆` appearing in the code to a call to `Subset.subset`
because the type class resolution should be able to figure out which `Subset`
instance is referred to. Thus the notation will be a simple:
-/

-- precedence is arbitrary for this example
infix:50 " ⊆ " => Subset.subset

/-!
Let's define a simple theory of sets to test it:
-/

-- a `Set` is defined by the elements it contains
-- -> a simple predicate on the type of its elements
def Set (α : Type u) := α → Prop

def Set.mem (x : α) (X : Set α) : Prop := X x

-- Integrate into the already existing typeclass for membership notation
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

instance : Subset (Set α) where
  subset X Y := ∀ (x : α), x ∈ X → x ∈ Y

example : ∀ (X : Set α), Set.empty ⊆ X := by
  intro X x
  -- ⊢ x ∈ Set.empty → x ∈ X
  intro h
  exact False.elim h -- empty set has no members

/-!
### Binders
Because declaring syntax that uses variable binders used to be a rather
unintuitive thing to do in Lean 3, we'll take a brief look at how naturally
this can be done in Lean 4.

For this example we will define the well-known notation for the set
that contains all elements `x` such that some property holds:
`{x ∈ ℕ | x < 10}` for example.

First things first we need to extend the theory of sets from above slightly:
-/

-- the basic "all elements such that" function for the notation
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
Equipped with this function, we can now attempt to intuitively define a
basic version of our notation:
-/
notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 } -- { x | x ≤ 1 } : Set Nat

example : 1 ∈ { (y : Nat) | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { (y : Nat) | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

/-!
This intuitive notation will indeed deal with what we could throw at
it in the way we would expect it.

As to how one might extend this notation to allow more set-theoretic
things such as `{x ∈ X | p x}` and leave out the parentheses around
the bound variables, we refer the reader to the macro chapter.


## Exercises

1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.

    **a)** Using `notation` command.
    **b)** Using `infix` command.
    **c)** Using `syntax` command.

    Hint: multiplication in Lean 4 is defined as `infixl:70 " * " => HMul.hMul`.

2. Consider the following syntax categories: `term`, `command`, `tactic`; and 3 syntax rules given below. Make use of each of these newly defined syntaxes.

    ```lean
      syntax "good morning" : term
      syntax "hello" : command
      syntax "yellow" : tactic
    ```

3. Create a `syntax` rule that would accept the following commands:

    - `red red red 4`
    - `blue 7`
    - `blue blue blue blue blue 18`

    (So, either all `red`s followed by a number; or all `blue`s followed by a number; `red blue blue 5` - shouldn't work.)

    Use the following code template:

    ```lean
    syntax (name := colors) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
    ```

4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.

    Create a `syntax` rule that would accept the following commands:

    - `#better_help option`
    - `#better_help option pp.r`
    - `#better_help option some.other.name`

    Use the following template:

    ```lean
    syntax (name := help) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"
    ```

5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:

    - `∑ x in { 1, 2, 3 }, x^2`
    - `∑ x in { "apple", "banana", "cherry" }, x.length`

    Use the following template:

    ```lean
    import Std.Classes.SetNotation
    import Std.Util.ExtendedBinder
    syntax (name := bigsumin) ...
    -- our "elaboration function" that infuses syntax with semantics
    @[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666
    ```

    Hint: use the `Std.ExtendedBinder.extBinder` parser.
    Hint: you need Std4 installed in your Lean project for these imports to work.

-/
