import Lean
import Lean.Meta
/-!
# `MetaM`

--todo
* metavariables, assignment, types of metavariables
* metavariables as goals
* local contexts, `withMVarContext`
* smart Expr constructors
* locally nameless representation; `forallTelescope` and friends
* implicit arguments, app builder (`mkAppM` etc.)
-/

/-!
## Smart constructors for expressions

Lean has smart helpers that allow construction of expressions with hygeine, reduction and other such details taken care of the system, and allow us to use the powerful unifier. 
Here we sketch a few of these.
-/

/-!
We first consider an example where we use `reduce : Expr → MetaM Expr` 
to reduce the expression for the sum of natural numbers. The rest of the code is as
seen in the chapter on Expressions.
-/
open Lean Meta 
def natExpr: Nat → Expr 
| 0 => mkConst ``Nat.zero
| n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)
#eval natExpr 3

def sumExpr : Nat → Nat → MetaM Expr 
| n, m => reduce <| mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]
#eval sumExpr 2 3

/-!
We next construct a λ-expression for the function `double : Nat → Nat` given by
`double n = n + n`. To construct such an expression, a free variable `n` has to be
introduced, the expression defined in terms of this variable, and the λ-expression
should be constructed. 

The variable is introduced by passing the code using it as a _continuation_ to 
`withLocalDecl`. The other arguments of `withLocalDecl` are the name of the variable,
the _binder_ that determines whether it is explicit, and the type of the variable.

The λ-expression is constructed using `mkLambdaFVars`, with the first argument being
an array of free variables (just one in this case) with respect to which we take λ.
The second argument is the body of the λ-expression.
-/
def double : MetaM Expr := do
  withLocalDecl `n BinderInfo.default (mkConst ``Nat)  fun n =>
    mkLambdaFVars #[n] <| mkAppN (mkConst ``Nat.add) #[n, n] 
#eval double

/-!
We check that `double` is indeed as claimed by applying it to an expression for `3`.
-/
def sixExpr : MetaM Expr := do
  let expr := mkApp (← double) (natExpr 3)
  let expr ← reduce expr
  return expr
#eval sixExpr

/-!
A powerful feature of lean is its unifier. There is an easy way to use this while
meta-programming, namely the method `mkAppM` (and a similar method `mkAppM'`).
For example, we can construct an expression for the length of a list using `mkAppM`.
Recall that `List.length` has an implicit parameter `α : Type u`. This is deduced by unification, as are universe levels.
-/
def lenExp (list: Expr) : MetaM Expr := do
  let expr ← mkAppM ``List.length #[list]
  let expr ← reduce expr
  return expr

/-!
We test the unification in this definition.
-/
def egList := [1, 3, 7, 8]
def egLen : MetaM Expr := 
  lenExp (mkConst ``egList)
#eval egLen

/-!
Analogous to the construction of λ-expressions, we can construct ∀-expressions 
(i.e., Π-expressions) for types. We simply replace `mkLambdaFVars` with `mkForallFVars`.

A special case of Π-types are function types `A → B`. These can be constructed using
the function `mkArrow`. Another very useful meta-level function is `mkEq`, which constructs equalities.

We illustrate all these, as well as the construction of a λ-expressions, by
constructing the proposition `∀ n: Nat, f n = f (n + 1)` as a function of `f`.
Formally this is `λ f, ∀ n, f n = f (n + 1)`. We break this into many steps to
illustrate the different ingredients.
-/
def localConstExpr: MetaM Expr := do
  let funcType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `f BinderInfo.default funcType fun f => do
  let feqn ← withLocalDecl `n BinderInfo.default (mkConst ``Nat) fun n => do
      let lhs := mkApp f n
      let rhs :=  mkApp f (← mkAppM ``Nat.succ #[n])
      let eqn ←  mkEq lhs rhs
      mkForallFVars #[n] eqn
  mkLambdaFVars #[f] feqn
#eval localConstExpr

/-!
As the above definition was rather complicated, it is better to check it.
A convenient way to do this is to use an _elaborator_ to assign the expression 
to a constant and then check it. We will explain elaborators in a future chapter.
-/
elab "localConstExpr!" : term => do
  localConstExpr 
#reduce localConstExpr! -- fun f => ∀ (n : Nat), f n = f (Nat.succ n)
