/-! # Syntax
This chapter is concerned with the means to declare and operate on syntax
in Lean. Since there are a multitude of ways to operate on it, we will
not go into great detail about this yet and postpone quite a bit of this to
later chapters.

## Declaring Syntax
### Declaration helpers
Some readers might be familiar with the `infix` or even the `notation`
commands, for those that are not here is a brief recap:
-/
-- XOR, denoted \oplus

infix:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l " LXOR " r => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

/-!
As we can see the `infix` command allows us to declare a notation for
a binary operation that is infix, meaning that the operator is in between
the operands (as opposed to e.g. before which would be done using the `prefix` command).
On the right hand side it expects a function that operates on these two parameters
and returns some value. The `notation` command on the other hand allows us some more
freedom, we can just "mention" the parameters right in the syntax definition
and operate on them on the right hand side. It gets even better though, we can
in theory create syntax with 0 up to as many parameters as we wish using the
`notation` command, it is hence also often referred to as "mixfix" notation.

The two unintuitive parts about these two are:
- The fact that we are leaving spaces around our operators: " ⊕ ", " XOR ".
  This is so that when Lean pretty prints our syntax later on it also
  uses spaces around the operators, otherwise the syntax would just be presented
  as `l⊕r` as opposed to `l ⊕ r`.
- The `60` and `10` right after the respective commands, these denote the operator
  precedence, meaning how strong they bind to their arguments, lets see this in action
-/

#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

/-!
As you can see the Lean interpreter analyzed the first term without parentheses
like the second instead of the third one. This is because the `⊕` notation
has higher precedence than `LXOR` (`60 > 10` after all) and is thus evaluated before it.
This is also how you might implement rules like `*` being evaluated before `+`.

### Free form syntax declarations
With the above `infix` and `notation` commands you can get quite far with
declaring ordinary mathematical syntax already, Lean does however allow you to
introduce arbitrarily complex syntax as well. This is done using two main commands
`syntax` and `declare_syntax_cat`. A `syntax` command allows you add a new
syntax rule to an already existing, so called, syntax category. The most common syntax
categories are:
- `term`, this category will be discussed in detail in the elaboration chapter,
  for now you can think of it as "the syntax of everything that has a value"
- `command`, this is the category for top level commands like `#check`, `def` etc.
- TODO: ...
Let's see this in action:
-/

syntax "MyTerm" : term

/-!
We can now write `MyTerm` in place of things like `1 + 1` and it will be
*syntactically* valid, this does not mean the code will compile yet,
it just means that the Lean parser can understand it:
-/

def Playground1.test := MyTerm
-- elaboration function for 'termMyTerm' has not been implemented
--   MyTerm

/-!
Implementing this so called "elaboration function", which will actually
give meaning to this syntax, is topic of the elaboration and macro chapter.
An example of one we have already seen however would be the `notation` and
`infix` command

We can of course also involve other syntax into our own declarations
in order to build up syntax trees, for example we could try to build our
own little boolean expression language:
-/

namespace Playground2

-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

/-!
TODO: Add the explanation on precedence to enforce associativity from
https://github.com/leanprover/lean4/blob/master/doc/metaprogramming-arith.md

While this does work, it allows arbitrary terms to the left and right of our
`AND` and `OR` operation. If we want to write a mini language that only accepts
our boolean language on a syntax level we will have to declare our own
syntax category on top. This is done using the `declare_syntax_cat` command:
-/

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax boolean_expr " OR " boolean_expr : boolean_expr
syntax boolean_expr " AND " boolean_expr : boolean_expr

/-!
Now that we are working in our own syntax category however we are completely
disconnected from the rest of the system, we can not be used in place of
terms anymore:
-/

#check ⊥ AND ⊤ -- expected term

/-!
In order to integrate our syntax category into the rest of the system we will
have to extend an already existing one with new syntax, in this case we
will re-embed it into the `term` category:
-/

syntax "[Bool|" boolean_expr "]" : term
#check [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes

/-!
### Syntax combinators
In order to declare more complex syntax it is often very desirable to have
some basic operations on syntax already built-in, these include:
- helper parsers without syntax categories (i.e. not extendable)
- alternatives
- repetetive parts
- optional parts
While all of these do have an encoding based on syntax categories this
can make things quite ugly at times so Lean provides a way to do all
of these.

In order to see all of these in action briefly we will define a simple
binary expression syntax.
First things first, declaring named parsers that don't belong to a syntax
category, this is quite similar to ordinary `def`s:
-/

syntax binOne := "O"
syntax binZero := "Z"

/-!
These named parsers can be used in the same positions as syntax categories
from above, their only difference to them is, that they are not extensible.
There does also exist a number of built-in named parsers that are generally useful,
most notably:
- `str` for string literals
- `num` for number literals
- `ident` for identifiers
- ... TOOD: better list or link to compiler docs

Next up we want to declare a parser that understands digits, a binary digit is
either 0 or 1 so we can write:
-/

syntax binDigit := binZero <|> binOne

/-!
Where the `<|>` operator implements the "accept the left or the right" behaviour.
We can also chain them to achieve parsers that accept arbitrarily many, arbitrarly complex
other ones. Now we will define the concept of a binary number, usually this would be written
as digits directly after each other but we will instead use comma separated ones to showcase
the repetetion feature:
-/

-- the "+" denotes "one or many", in order to achieve "zero or many" use "*" instead
-- the "," denotes the separator between the `binDigit`s, if left out the default separator is a space
syntax binNumber := binDigit,+

/-!
Since we can just used named parsers in place of syntax categories we can now easily
add this to the `term` category:
-/

syntax "bin(" binNumber ")" : term
#check bin(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
Note that nothing is limiting us to only using one syntax combinator per parser,
we could also have written all of this inline:
-/

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
#check binCompact(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
As a final feature lets add an optional string comment that explains the binary
literal being declared:
-/

-- The (...)? syntax makes the part in parentheses optional
syntax "binDoc(" (str ";")? binNumber ")" : term
#check binDoc(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check binDoc("mycomment"; Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
## Operating on Syntax
### Matching on Syntax
### Constructing new Syntax
-/
