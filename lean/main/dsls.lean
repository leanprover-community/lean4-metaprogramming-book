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
We have arithmetic expressions, boolean expressions, and commands.
-/

/-
#### Arithmetic Expressions

Arithmetic expressions are naturals, variables, or sums of other
arithmetic expressions.
-/
inductive AExp
| ANat: Nat -> AExp
| AVar: String -> AExp
| APlus: AExp -> AExp -> AExp
deriving Inhabited

/-
#### Boolean Expressions

Boolean expressions are either booleans (true/false), variables,
an and (`&&`) of two booleans, or a less than comparison (`<`) between
two arithmetic expressions.
-/
inductive BExp
| BBool: Bool -> BExp
| BVar: String -> BExp
| BAnd: BExp -> BExp -> BExp
| BLess: AExp -> AExp -> BExp
deriving Inhabited

/-
#### Command

Commands can be either a `skip` command to skip the execution, an `assign`
command to assign a value to a variable, a `seq`(`;;`) to sequence commands,
an `if` for conditionals, and `while` for looping.
-/
inductive Command
| Skip: Command
| Assign: String -> AExp -> Command
| Seq: Command -> Command -> Command
| If: BExp -> Command -> Command -> Command
| While: BExp -> Command -> Command
deriving Inhabited


/-
## Embedding a DSL via Low-level Syntax Elaboration

In this section, we shall contrast the previously explained
macro-based approach (which has type `Syntax → MacroM Syntax`)
with the lower level elaborator (which has type `Syntax → TermElabM Expr`)
that is the focus of this section.
-/

/-
#### Parsing AExp via Syntax Elaboration
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
   `(AExp.ANat $(nStx)) -- return the syntax.

def eg_AExp_num_macro: AExp := [imp_aexp| 42]
#reduce eg_AExp_num_macro

/-
In contrast to this approach, when we write an `elab`orator,
we are returning values in `Expr`, which is the core Lean
data type that Syntax is finally reduced down to. `Expr`
only contains the bare minimum to express a dependently typed language,
so as we shall see, building `Expr`s will be more laborious.

We shall use a `match` syntax which is of the form:

```
match <syntax-node> with
| `(<syntax-category>| <match-pattern>) => <rhs>
```

This means that we are looking for `Syntax` nodes whose syntax
category is `<syntax-category>`, which match the `<match-pattern>`.

To write a low level `elab`orator for `num`,
we write a combinator `mkApp': Name → Expr → Expr`
that create an `Expr` denoting the function application of a 
name `name` to an expression `e`.
-/


def elab_AExp_num (s: Syntax): TermElabM Expr :=
match s with
| `(imp_aexp| $n:num) => 
        -- build an Expr by hand
        mkAppM ``AExp.ANat #[ mkNatLit n.toNat ]
| _ => do 
   dbg_trace "elab_AExp_num failed"
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

elab "[imp_aexp'|" s:imp_aexp  "]" : term => elab_AExp_num s

/-
We invoke this on the number 42, and we do get out an `AExp.ANat 42`:
-/

def eg_AExp_num_elab: AExp := [imp_aexp'| 42]
#reduce eg_AExp_num_elab
-- AExp.ANat 42

/-
Let's write a macro_rules for converting identifiers.
We see that we need to grab the string as `nameStr`, then
quote the string back into `Syntax`, and then we finally build
the `AExp.Avar`.
-/
macro_rules
| `([imp_aexp| $name:ident ]) => do
   let nameStr : String := name.getId.toString
   let nameStx : Syntax := Lean.quote nameStr
   `(AExp.AVar $(nameStx))

def eg_AExp_ident_macro: AExp := [imp_aexp|  foo]
#reduce eg_AExp_ident_macro
-- AExp.AVar "foo"

/-
In contrast to the `macro_rules` based solution, see that
we build the expression node by hand, using lower level
functions such as `mkAppM` to build a function application,
and `mkStrLit: String → Expr` to convert a string into an `Expr`.
-/
def elab_aexp_ident (s: Syntax): TermElabM Expr :=
match s with 
| `(imp_aexp| $n:ident) =>
      mkAppM ``AExp.AVar #[mkStrLit n.getId.toString]
| _ => do 
  dbg_trace "elab_aexp_ident failed."
  throwUnsupportedSyntax


/-
We add our `elab` rule, which says that we can try to elaborate
a `s:imp_aexp` with `elab_aexp_ident`. 
-/
elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_ident s

def eg_AExp_ident_elab: AExp := [imp_aexp'|  foo]
#reduce eg_AExp_ident_elab
-- AExp.AVar "foo"

/-
We test that our new elaboration rule did not interfere with 
our previous rule to parse numbers:
-/
def eg_AExp_num2_elab: AExp := [imp_aexp'|  43]
#reduce eg_AExp_num2_elab
-- elab_aexp_ident failed.
-- AExp.AVar "43"

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

def eg_AExp_fail: AExp := [imp_aexp'| 42 + 43]
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
      `(AExp.APlus $xStx $yStx)

def eg_aexp_plus_macro: AExp := [imp_aexp| foo + bar]
#reduce eg_aexp_plus_macro
-- AExp.APlus (AExp.AVar "foo") (AExp.AVar "bar")



/-
This time, to recursively expand `imp_aexp`, we use
`Term.elabTerm`.  
-/

def elab_aexp_plus (s: Syntax): TermElabM Expr := 
match s with 
| `(imp_aexp| $x:imp_aexp + $y:imp_aexp) => do 
     let xExpr <- Term.elabTerm (<- `([imp_aexp'| $x])) none
     let yExpr <- Term.elabTerm (<- `([imp_aexp'| $y])) none
     mkAppM ``AExp.APlus #[xExpr, yExpr]
| _ => do 
   dbg_trace "elab_aexp_plus failed"
   throwUnsupportedSyntax


elab "[imp_aexp'|" s:imp_aexp "]" : term => elab_aexp_plus s
def eg_aexp_plus_elab: AExp := [imp_aexp'| foo + bar]
#print eg_aexp_plus_elab
-- AExp.APlus (AExp.AVar "foo") (AExp.AVar "bar")


/-
#### Parsing BExp

We repeat the same process, this time for `BExp`.
This time, we show a different method to writing the elaboration
function `elab_bexp: Syntax → TermElabM Expr`, where we write
the function as a regular lean function, and use regular recursion
to elaborate our `BExp`.
-/


declare_syntax_cat imp_bexp
syntax ident : imp_bexp
syntax imp_aexp "<" imp_aexp : imp_bexp
syntax imp_bexp "&&" imp_bexp : imp_bexp

-- Helper to convert Booleans into expressions
def mkBoolLit: Bool -> Expr
| true => mkConst ``Bool.true
| false => mkConst ``Bool.false


-- As we saw before, we can elaborate `AExp` by using `elabTerm`. Let's
-- write a helper for this as well

partial def elab_bexp (s: Syntax): TermElabM Expr := 
match s with
| `(imp_bexp| $n:ident) =>
     let str := n.getId.toString
     match str with 
     | "true" => mkAppM ``BExp.BBool #[mkBoolLit true]
     | "false" => mkAppM ``BExp.BBool #[mkBoolLit false]
     | n => mkAppM ``BExp.BVar #[mkStrLit str]

/-
To elaborate `aexp`s, we wrie a helper called `elab_aexp`, that calls
`elabTerm` on the term `[imp_aexp'| $s]`. This produces an `Expr` node,
which we use to build a `BExp.BLess`
-/
| `(imp_bexp| $x:imp_aexp < $y:imp_aexp) => do  
     let elab_aexp (s: Syntax): TermElabM Expr := do
        Term.elabTerm (<- `([imp_aexp'| $s])) none
       let x <- elab_aexp x
       let y <- elab_aexp y
       mkAppM ``BExp.BLess #[x, y]
/-
To elaborate `bexp`s, we recursively call `elab_bexp` to elaborate
the left and the right hand side, and we then finally create a `BExp.BAnd`
term.
-/
| `(imp_bexp| $x:imp_bexp && $y:imp_bexp) => do
     let x <- elab_bexp x -- recursion  
     let y <- elab_bexp y -- recursion
     mkAppM ``BExp.BAnd #[x, y]
| _ => throwUnsupportedSyntax


/- 
Finally, we write the elaborator rule that invokes the function
`elab_bexp` upon seeing an `[imp_bexp|...]`.
-/

elab "[imp_bexp|" s:imp_bexp "]" : term => elab_bexp s 


def eg_bexp_true : BExp := [imp_bexp| true]
#print eg_bexp_true
-- BExp.BBool true

def eg_bexp_false : BExp := [imp_bexp| false]
#print eg_bexp_false
-- BExp.BBool false

def eg_bexp_ident : BExp := [imp_bexp| var]
#print eg_bexp_ident
-- BExp.BVar "var"





def eg_bexp_lt_1 : BExp := [imp_bexp| 1 < 2]
#print eg_bexp_lt_1
-- BExp.BLess (AExp.ANat 1) (AExp.ANat 2)

def eg_bexp_lt_2 : BExp := [imp_bexp| 1 + 1 < 2 + 2]
#print eg_bexp_lt_2
-- BExp.BLess (AExp.ANat 1) (AExp.ANat 2)

def eg_bexp_and_1: BExp := [imp_bexp| true && true]
#print eg_bexp_and_1
-- BExp.BAnd (BExp.BBool true) (BExp.BBool true)

def eg_bexp_and_2: BExp := [imp_bexp| a < b && c < d]
#print eg_bexp_and_2
-- BExp.BAnd (BExp.BLess (AExp.AVar "a") (AExp.AVar "b"))
--           (BExp.BLess (AExp.AVar "c") (AExp.AVar "d"))

def eg_bexp_and_3: BExp := [imp_bexp| x + y < z && p + q < r]
#print eg_bexp_and_3
-- BExp.BAnd
--    (BExp.BLess (AExp.APlus (AExp.AVar "x") (AExp.AVar "y"))
--                (AExp.AVar "z"))
--    (BExp.BLess (AExp.APlus (AExp.AVar "p") (AExp.AVar "q"))
--                (AExp.AVar "r"))

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
syntax "if" imp_bexp "then" imp_command "else" imp_command "fi" : imp_command
syntax "while" imp_bexp "do" imp_command "od" : imp_command

partial def elabCommand (s: Syntax): TermElabM Expr := 
match s with
| `(imp_command| $x:ident = $e:imp_aexp) => do 
    let xString : String := x.getId.toString
    let elab_aexp (s: Syntax): TermElabM Expr := do
        Term.elabTerm (<- `([imp_aexp'| $s])) none
    let e <- elab_aexp e
    mkAppM ``Command.Assign #[(mkStrLit xString),e]
| `(imp_command| if $b:imp_bexp then $c:imp_command else $c':imp_command fi) => do 
     let b <- elab_bexp b
     let c <- elabCommand c -- recursion
     let c' <- elabCommand c' -- recursion
     mkAppM ``Command.If #[b, c, c']
| `(imp_command| while $b:imp_bexp do $c:imp_command od) => do 
     let b <- elab_bexp b
     let c <- elabCommand c
     mkAppM ``Command.While #[b, c]
| _ => throwUnsupportedSyntax
    
 
elab "[imp_command|" s:imp_command "]" : term => elabCommand s

def eg_command_assign : Command := [imp_command| x = 11 + 20]
#print eg_command_assign
-- Command.Assign "x" (AExp.APlus (AExp.ANat 10) (AExp.ANat 20))

def eg_command_if : Command := [imp_command| if 1 < 2 then x = 10 else x = 20 fi]
#print eg_command_if
-- Command.If (BExp.BLess (AExp.ANat 1) (AExp.ANat 2))
--  (Command.Assign "x" (AExp.ANat 10))
--  (Command.Assign "x" (AExp.ANat 20))
def eg_command_while : Command := [imp_command| while x < 3 do x = x + 10 od]
#print eg_command_while
-- Command.While
--  (BExp.BLess (AExp.AVar "x") (AExp.ANat 3))
--  (Command.Assign "x" (AExp.APlus (AExp.AVar "x") (AExp.ANat 10)))

-- | TODO: is this too low level? Should we just use sepBy and call it a day?
/-
A placeholder with precedence `p` accepts only notations with precedence at
least `p` in that place.  Thus the string `a + b + c` cannot be parsed as the
equivalent of `a + (b + c)` because the right-hand side operand of an `infixl`
notation has precedence one greater than the notation itself.
-/

syntax:60 imp_command:61 ";;" imp_command:60 : imp_command

/- Once again, we hijack the elaborator by adding a new rule to the elaboration -/

partial def elabCompound (x: Syntax) : TermElabM Expr :=
match x with
| `(imp_command| $a:imp_command ;; $b:imp_command) => do 
      let a <- elabCompound a
      let b <- elabCompound b 
      mkAppM ``Command.Seq #[a, b]
| other => elabCommand other -- hook into previous elaborator.

elab "[imp_command|" x:imp_command "]" : term => elabCompound x

def eg_command_seq : Command := [imp_command| x = 1 ;; x = 2 ;; x = 3 ;; x = 4]
#print eg_command_seq
-- Command.Seq (Command.Assign "x" (AExp.ANat 1))
--  (Command.Seq (Command.Assign "x" (AExp.ANat 2)) (Command.Assign "x" (AExp.ANat 3)))

/-
At this point, we have defined the full parsing infrastructure.
-/

def eg_command_all := [imp_command|
  x = 1 ;;
  y = 0 ;;
  while x < 10 do 
    y = y + 1
  od ;;
  if x < 10
  then y = y + 2
  else y = y + 3
  fi
]
#print eg_command_all
-- Command.Seq (Command.Assign "x" (AExp.ANat 1))
--   (Command.Seq (Command.Assign "y" (AExp.ANat 0))
--     (Command.Seq
--       (Command.While (BExp.BLess (AExp.AVar "x") (AExp.ANat 10))
--         (Command.Assign "y" (AExp.APlus (AExp.AVar "y") (AExp.ANat 1))))
--       (Command.If (BExp.BLess (AExp.AVar "x") (AExp.ANat 10))
--         (Command.Assign "y" (AExp.APlus (AExp.AVar "y") (AExp.ANat 2)))
--         (Command.Assign "y" (AExp.APlus (AExp.AVar "y") (AExp.ANat 3))))))



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

/-
#### What is a syntax category, exactly?

A syntax category is information that is stored in a `Syntax` node about 
which nonterminal it belongs to. Intuitively, a grammar contains rules such as:

```
Expr -> Term
Term -> Factor
Factor -> number
```

and it is thus important to know whether a given token `42` is a `Factor`, or a `Term`,
or an `Expr`, since it could conceivably be any of these, by the derivations `Factor -> Number`,
`Term -> Factor -> Number`, and `Expr -> Term -> Factor -> Number` respectively.
-/
