/-
## DSLs in Lean

In this tutorial, we shall write a DSL for [IMP](http://concrete-semantics.org/concrete-semantics.pdf),
which is a simple imperative language.
-/
import Lean
import Lean.Elab.Deriving.Basic
open Lean Lean.Syntax
open Lean.Elab
open Lean.Elab.Command
open Lean.Meta
open Lean

/--
We begin by defining the AST of the language:
-/

/-
Arithmetic expressions are naturals, variables, or sums of other
arithmetic expressions.
-/
inductive Aexp
| ANat: Nat -> Aexp
| AVar: String -> Aexp
| APlus: Aexp -> Aexp -> Aexp
deriving Inhabited

/-
Boolean expressions are either booleans (true/false), variables,
an and (`&&`) of two booleans, or a less than comparison (`<`) between
two arithmetic expressions.
-/
inductive Bexp
| BBool: Bool -> Bexp
| BVar: String -> Bexp
| BAnd: Bexp -> Bexp -> Bexp
| BLess: Aexp -> Aexp -> Bexp
deriving Inhabited

/-
Commands can be either a `skip` command to skip the execution, an `assign`
command to assign a value to a variable, a `seq`(`;;`) to sequence commands,
an `if` for conditionals, and `while` for looping.
-/
inductive Command
| Skip: Command
| Assign: String -> Aexp -> Command
| Seq: Command -> Command -> Command
| If: Bexp -> Command -> Command -> Command
| While: Bexp -> Command -> Command
deriving Inhabited


/-
## Embedding a DSL via Low-level Elaboration

In this section, we shall contrast the previously explained
macro-based approach (which has type `Syntax → MacroM Syntax`)
with the lower level elaborator (which has type `Syntax → TermElabM Expr`)
that is the focus of this section.
-/

/-
#### Parsing aexp
-/


declare_syntax_cat imp_aexp
syntax num : imp_aexp
syntax ident : imp_aexp
syntax imp_aexp "+" imp_aexp : imp_aexp

/- 
Recall that if we were doing this via lean macros, 
we would write out an "interpretation" macro such as `[imp_aexp|...]`,
and the declare the translation as a macro rule:
-/

syntax "[imp_aexp|" imp_aexp "]" : term
macro_rules
| `([imp_aexp| $n:num ]) => do
   let n : Nat := n.toNat -- grab the number.
   let nStx : Syntax := Lean.quote n -- quote the number.
   `(Aexp.ANat $(nStx)) -- return the syntax.

def eg_aexp_num_macro: Aexp := [imp_aexp| 42]
#reduce eg_aexp_num_macro

/-
In contrast to this approach, when we write an `elab`orator,
we are returning values in `Expr`, which is the core Lean
data type that Syntax is finally reduced down to. `Expr`
only contains the bare minimum to express a dependently typed language,
so as we shall see, building `Expr`s will be more laborious.

The lower level match syntax is of the form 

```
match <syntax-node> with
| `(syntax<category>| <match-pattern>) => <rhs>
```

First, we write a combinator `mkApp': Name → Expr → Expr`
that create an `Expr` denoting the function application of a 
name `name` to an expression `e`.
-/


def elab_aexp_num (s: Syntax): TermElabM Expr :=
match s with
| `(imp_aexp| $n:num) => 
        -- build an Expr by hand
        mkAppM ``Aexp.ANat #[ mkNatLit n.toNat ]
| _ => do 
   dbg_trace "elab_aexp_num failed"
   throwUnsupportedSyntax

/-
Note that we are building a raw `Expr` by hand. Also note that
we `throwUnsupportedSyntax`, to tell Lean that we were unable
to parse the `Syntax` node, and would like Lean to try other parsers
that might be able to parse the given `Syntax`. This makes the infrastructure
*extensible*.
-/

/-
To test that our parser works, let's write an "evaluator" elaborator,
much as we do when writing macros, called `[imp_aexp'|...]` which takes
an `imp_aexp` and produces an `Expr`:
-/

elab "[imp_aexp'|" s:imp_aexp  "]" : term => elab_aexp_num s

/-
We invoke this on the number 42, and we do get out an `Aexp.ANat 42`:
-/

def eg_aexp_num_elab: Aexp := [imp_aexp'| 42]
#reduce eg_aexp_num_elab
-- Aexp.ANat 42

/-
Let's write a macro_rules for converting identifiers.
We see that we need to grab the string as `nameStr`, then
quote the string back into `Syntax`, and then we finally build
the `Aexp.Avar`.
-/
macro_rules
| `([imp_aexp| $name:ident ]) => do
   let nameStr : String := name.getId.toString
   let nameStx : Syntax := Lean.quote nameStr
   `(Aexp.AVar $(nameStx))

def eg_aexp_ident_macro: Aexp := [imp_aexp|  foo]
#reduce eg_aexp_ident_macro
-- Aexp.AVar "foo"

/-
In contrast to the `macro_rules` based solution, see that
we build the expression node by hand, using lower level
functions such as `mkAppM` to build a function application,
and `mkStrLit: String → Expr` to convert a string into an `Expr`.
-/
def elab_aexp_ident (s: Syntax): TermElabM Expr :=
match s with 
| `(imp_aexp| $n:ident) =>
      mkAppM ``Aexp.AVar #[mkStrLit n.getId.toString]
| _ => do 
  dbg_trace "elab_aexp_ident failed."
  throwUnsupportedSyntax


/-
We add our `elab` rule, which says that we can try to elaborate
a `s:imp_aexp` with `elab_aexp_ident`. 
-/
elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_ident s

def eg_aexp_ident_elab: Aexp := [imp_aexp'|  foo]
#reduce eg_aexp_ident_elab
-- Aexp.AVar "foo"

/-
We test that our new elaboration rule did not interfere with 
our previous rule to parse numbers:
-/
def eg_aexp_num2_elab: Aexp := [imp_aexp'|  43]
#reduce eg_aexp_num2_elab
-- elab_aexp_ident failed.
-- Aexp.AVar "43"

/-
See that we have *not* lost the ability to parse numbers when we introduced
our new `elab_aexp_ident` rule, even though the two declarations look identical
on the left-hand-side of the rule:

```
elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_num name
elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_ident name
```

This is because, as we discussed above, introducing new `elab` rules ensures
that these rules are run in sequence, and this allows for the Lean syntax
to be extended gracefully in an open-ended fashion.

We can see from the output that Lean did try to runthe rule `elab_aexp_ident` which failed.
It then fell back to running `elab_aexp_num`, which succeeded.
-/

/-
We can try a piece of grammar that has not been handled yet, and see how both elaborators
will be invoked in succession:
-/

def eg_aexp_fail: Aexp := [imp_aexp'| 42 + 43]
-- elab_aexp_ident failed.
-- elab_aexp_num failed

/-
Clearly, both parses `elab_aexp_ident` and `elab_aexp_num`
are tried in succession, and both fail, leading to an error.
-/



/-
We shall fix this omission, and finally parse the addition node, first as a macro rule:
-/

macro_rules
| `([imp_aexp| $x:imp_aexp + $y:imp_aexp]) => do
      let xStx <- `([imp_aexp| $(x)])
      let yStx <- `([imp_aexp| $(y)])
      `(Aexp.APlus $xStx $yStx)

def eg_aexp_plus_macro: Aexp := [imp_aexp| foo + bar]
#reduce eg_aexp_plus_macro
-- Aexp.APlus (Aexp.AVar "foo") (Aexp.AVar "bar")

/-
This time, to recursively expand `imp_aexp`, we use
`Term.elabTerm`.
-/

def elab_aexp_plus (s: Syntax): TermElabM Expr := 
match s with 
| `(imp_aexp| $x:imp_aexp + $y:imp_aexp) => do 
     let xExpr <- Term.elabTerm (<- `([imp_aexp'| $x])) none
     let yExpr <- Term.elabTerm (<- `([imp_aexp'| $y])) none
     mkAppM ``Aexp.APlus #[xExpr, yExpr]
| _ => do 
   dbg_trace "elab_aexp_plus failed"
   throwUnsupportedSyntax


elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_plus s
def eg_aexp_plus_elab: Aexp := [imp_aexp'| foo + bar]
#print eg_aexp_plus_elab
-- Aexp.APlus (Aexp.AVar "foo") (Aexp.AVar "bar")


/-
#### Parsing BExp

We repeat the same process, this time for `BExp`.
-/

declare_syntax_cat imp_bexp
syntax ident : imp_bexp

/-
Note that we want `<` to have lower precedence than `+`,
whch we declare by annotating the parse rule with `syntax:min`.
-/

/-
Once again, we declare the macro `[imp_bexp|...]` which takes
an `imp_exp` and produces a Lean `term`.
-/
syntax "[imp_bexp| " imp_bexp "]" : term

/-
We write the macro rule once more:
-/

macro_rules
| `([imp_bexp| $x:ident]) => do
    let xStr : String := x.getId.toString
    match xStr with
    | "true" => `(Bexp.BBool true)
    | "false" => `(Bexp.BBool false)
    | _ => do
       let xStx : Syntax := quote xStr
       `(Bexp.BVar $xStx)

def eg_bexp_true : Bexp := [imp_bexp| true]
#print eg_bexp_true
-- BExp.BBool true

def eg_bexp_false : Bexp := [imp_bexp| false]
#print eg_bexp_false
-- BExp.BBool false

def eg_bexp_ident : Bexp := [imp_bexp| var]
#print eg_bexp_ident
-- BExp.BVar "var"


syntax:30 imp_aexp "<" imp_aexp : imp_bexp


macro_rules
| `([imp_bexp| $x:imp_aexp < $y:imp_aexp]) =>
      `(Bexp.BLess [imp_aexp| $x] [imp_aexp| $y])

def eg_bexp_lt_1 : Bexp := [imp_bexp| 1 < 2]
#print eg_bexp_lt_1
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

def eg_bexp_lt_2 : Bexp := [imp_bexp| 1 + 1 < 2 + 2]
#print eg_bexp_lt_2
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

syntax:20 imp_bexp "&&" imp_bexp : imp_bexp
macro_rules
| `([imp_bexp| $x:imp_bexp && $y:imp_bexp]) => do
    `(Bexp.BAnd [imp_bexp| $x] [imp_bexp| $y])

def eg_bexp_and_1: Bexp := [imp_bexp| true && true]
#print eg_bexp_and_1
-- Bexp.BAnd (Bexp.BBool true) (Bexp.BBool true)

def eg_bexp_and_2: Bexp := [imp_bexp| a < b && c < d]
#print eg_bexp_and_2
-- Bexp.BAnd (Bexp.BLess (Aexp.AVar "a") (Aexp.AVar "b"))
--           (Bexp.BLess (Aexp.AVar "c") (Aexp.AVar "d"))

def eg_bexp_and_3: Bexp := [imp_bexp| x + y < z && p + q < r]
#print eg_bexp_and_3
-- Bexp.BAnd
--    (Bexp.BLess (Aexp.APlus (Aexp.AVar "x") (Aexp.AVar "y"))
--                (Aexp.AVar "z"))
--    (Bexp.BLess (Aexp.APlus (Aexp.AVar "p") (Aexp.AVar "q"))
--                (Aexp.AVar "r"))

/-
See that our annotations ensure that we parse precedence
correctly. We correctly bind `+` tighter than `<`,
and `<` tighter than `&&`.
-/


/-
#### Parsing commands

We'll parse the final piece of the puzzle, the commands.
It's going to be old hat at this point, and we follow the hopefully
well-understood formula.
-/

declare_syntax_cat imp_command

syntax ident "=" imp_aexp : imp_command

syntax "[imp_command|" imp_command "]" : term

macro_rules
| `([imp_command| $x:ident = $exp:imp_aexp]) => do
      let xString : String := x.getId.toString
      let xStx : Syntax := quote xString
      `(Command.Assign $(xStx) [imp_aexp| $exp])

def eg_command_assign : Command := [imp_command| x = 11 + 20]
#print eg_command_assign
-- Command.Assign "x" (Aexp.APlus (Aexp.ANat 10) (Aexp.ANat 20))

syntax "if'" imp_bexp "then" imp_command "else" imp_command : imp_command

macro_rules
| `([imp_command| if' $b:imp_bexp then $t:imp_command else $e:imp_command]) => do
      `(Command.If [imp_bexp| $b] [imp_command| $t] [imp_command| $e])

def eg_command_if : Command := [imp_command| if' 1 < 2 then x = 10 else x = 20]
#print eg_command_if
-- Command.If (Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2))
--  (Command.Assign "x" (Aexp.ANat 10))
--  (Command.Assign "x" (Aexp.ANat 20))

syntax "while" imp_bexp "do" imp_command : imp_command
macro_rules
| `([imp_command| while $b:imp_bexp do $t:imp_command]) => do
     `(Command.While [imp_bexp| $b] [imp_command| $t])

def eg_command_while : Command := [imp_command| while x < 3 do x = x + 10]
#print eg_command_while
-- Command.While
--  (Bexp.BLess (Aexp.AVar "x") (Aexp.ANat 3))
--  (Command.Assign "x" (Aexp.APlus (Aexp.AVar "x") (Aexp.ANat 10)))

/-
A placeholder with precedence `p` accepts only notations with precedence at
least `p` in that place.  Thus the string `a + b + c` cannot be parsed as the
equivalent of `a + (b + c)` because the right-hand side operand of an `infixl`
notation has precedence one greater than the notation itself.
-/

syntax:60 imp_command:61 ";;" imp_command:60 : imp_command

macro_rules
| `([imp_command| $x ;; $y ]) => do
      `(Command.Seq [imp_command| $x] [imp_command| $y])

def eg_command_seq : Command := [imp_command| x = 1 ;; x = 2 ;; x = 3 ;; x = 4]
#print eg_command_seq
-- Command.Seq (Command.Assign "x" (Aexp.ANat 1))
--  (Command.Seq (Command.Assign "x" (Aexp.ANat 2)) (Command.Assign "x" (Aexp.ANat 3)))

/-
Compare the above to an "incorrect" parse, given by defining the
precedences in the opposite way:
-/

syntax:60 imp_command:60 ";×;" imp_command:61 : imp_command

macro_rules
| `([imp_command| $x ;×; $y ]) => do
      `(Command.Seq [imp_command| $x] [imp_command| $y])


def eg_command_seqx : Command := [imp_command| x = 1 ;×; x = 2 ;×; x = 3 ;×; x = 4]
#print eg_command_seqx
-- Command.Seq
-- |(Command.Seq
-- |  (Command.Seq
-- |  | (Command.Assign "x" (Aexp.ANat 1))
-- |  | (Command.Assign "x" (Aexp.ANat 2)))
-- |  (Command.Assign "x" (Aexp.ANat 3)))
-- |(Command.Assign "x" (Aexp.ANat 4))


/-
At this point, we have defined the full parsing infrastructure.
-/


/-
# FAQ
-/
/-
#### How do I debug a `macro_rule`?

Use `dbg_trace` to print any information.
-/

syntax "[faq_debug|" term "]" :  term
macro_rules
| `([faq_debug| $x:term ]) => do
      dbg_trace x
      return x

def eg_faq_debugg : Int := [faq_debug| 1 + 2 + 3]
-- («term_+_» («term_+_» (num "1") "+" (num "2")) "+" (num "3"))

/-
#### How do I throw an errror from a macro?

Use `MacroM.throw: String → MacroM α
-/

syntax "[faq_error|" term "]" :  term
macro_rules
| `([faq_error| $x:term ]) => do
      Macro.throwError "error!"
      return x

def eg_faq_error : Int := [faq_error| 42]
-- error!
