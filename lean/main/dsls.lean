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

abbrev vname := String

inductive Aexp
| ANat: Nat -> Aexp
| AVar: String -> Aexp
| APlus: Aexp -> Aexp -> Aexp
deriving Inhabited

inductive Bexp
| BBool: Bool -> Bexp
| BVar: String -> Bexp
| BAnd: Bexp -> Bexp -> Bexp
| BLess: Aexp -> Aexp -> Bexp
deriving Inhabited

inductive Command
| Skip: Command
| Assign: vname -> Aexp -> Command
| Seq: Command -> Command -> Command
| If: Bexp -> Command -> Command -> Command
| While: Bexp -> Command -> Command
deriving Inhabited


/-
## Direct parsing by macros
-/

/-
#### Parsing aexp
-/

declare_syntax_cat imp_aexp
syntax num : imp_aexp
syntax ident : imp_aexp
syntax imp_aexp "+" imp_aexp : imp_aexp

syntax "[imp_aexp|" imp_aexp "]" : term

macro_rules
| `([imp_aexp| $n:num ]) => do
   let n : Nat := n.toNat
   let nStx : Syntax := Lean.quote n
   `(Aexp.ANat $(nStx))

def example_aexp_num: Aexp := [imp_aexp| 42]
#reduce example_aexp_num
-- Aexp.ANat 42

macro_rules
| `([imp_aexp| $name:ident ]) => do
   let nameStr : String := name.getId.toString
   let nameStx : Syntax := Lean.quote nameStr
   `(Aexp.AVar $(nameStx))


def example_aexp_ident: Aexp := [imp_aexp| foo]
#reduce example_aexp_ident
-- Aexp.AVar "foo"

macro_rules
| `([imp_aexp| $x:imp_aexp + $y:imp_aexp]) => do
      let xStx <- `([imp_aexp| $(x)])
      let yStx <- `([imp_aexp| $(y)])
      `(Aexp.APlus $xStx $yStx)


def example_aexp_plus: Aexp := [imp_aexp| foo + bar]
#reduce example_aexp_plus
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

def example_bexp_true : Bexp := [imp_bexp| true]
#print example_bexp_true
-- BExp.BBool true

def example_bexp_false : Bexp := [imp_bexp| false]
#print example_bexp_false
-- BExp.BBool false

def example_bexp_ident : Bexp := [imp_bexp| var]
#print example_bexp_ident
-- BExp.BVar "var"


syntax:30 imp_aexp "<" imp_aexp : imp_bexp


macro_rules
| `([imp_bexp| $x:imp_aexp < $y:imp_aexp]) =>
      `(Bexp.BLess [imp_aexp| $x] [imp_aexp| $y])

def example_bexp_lt_1 : Bexp := [imp_bexp| 1 < 2]
#print example_bexp_lt_1
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

def example_bexp_lt_2 : Bexp := [imp_bexp| 1 + 1 < 2 + 2]
#print example_bexp_lt_2
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

syntax:20 imp_bexp "&&" imp_bexp : imp_bexp
macro_rules
| `([imp_bexp| $x:imp_bexp && $y:imp_bexp]) => do
    `(Bexp.BAnd [imp_bexp| $x] [imp_bexp| $y])

def example_bexp_and_1: Bexp := [imp_bexp| true && true]
#print example_bexp_and_1
-- Bexp.BAnd (Bexp.BBool true) (Bexp.BBool true)

def example_bexp_and_2: Bexp := [imp_bexp| a < b && c < d]
#print example_bexp_and_2
-- Bexp.BAnd (Bexp.BLess (Aexp.AVar "a") (Aexp.AVar "b"))
--           (Bexp.BLess (Aexp.AVar "c") (Aexp.AVar "d"))

def example_bexp_and_3: Bexp := [imp_bexp| x + y < z && p + q < r]
#print example_bexp_and_3
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

def example_command_assign : Command := [imp_command| x = 10 + 20]
#print example_command_assign
-- Command.Assign "x" (Aexp.APlus (Aexp.ANat 10) (Aexp.ANat 20))

syntax "if'" imp_bexp "then" imp_command "else" imp_command : imp_command

macro_rules
| `([imp_command| if' $b:imp_bexp then $t:imp_command else $e:imp_command]) => do
      `(Command.If [imp_bexp| $b] [imp_command| $t] [imp_command| $e])

def example_command_if : Command := [imp_command| if' 1 < 2 then x = 10 else x = 20]
#print example_command_if
-- Command.If (Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2))
--  (Command.Assign "x" (Aexp.ANat 10))
--  (Command.Assign "x" (Aexp.ANat 20))

syntax "while" imp_bexp "do" imp_command : imp_command
macro_rules
| `([imp_command| while $b:imp_bexp do $t:imp_command]) => do
     `(Command.While [imp_bexp| $b] [imp_command| $t])

def example_command_while : Command := [imp_command| while x < 3 do x = x + 10]
#print example_command_while
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

def example_command_seq : Command := [imp_command| x = 1 ;; x = 2 ;; x = 3 ;; x = 4]
#print example_command_seq
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


def example_command_seqx : Command := [imp_command| x = 1 ;×; x = 2 ;×; x = 3 ;×; x = 4]
#print example_command_seqx
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

def faq_debug_example : Int := [faq_debug| 1 + 2 + 3]
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

def faq_error_example : Int := [faq_error| 42]
-- error!
