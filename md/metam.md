```lean
import Lean
```

# `MetaM`

--todo
* metavariables, assignment, types of metavariables
* metavariables as goals
* local contexts, `withMVarContext`
* smart Expr constructors
* locally nameless representation; `forallTelescope` and friends
* implicit arguments, app builder (`mkAppM` etc.)

## Smart constructors for expressions

Lean has smart helpers that allow construction of expressions with hygeine,
reduction and other such details taken care of the system, and allow us to use
the powerful unifier. Here we sketch a few of these.

But first, let's recap the definition of `natExpr`

```lean
open Lean Meta

def natExpr : Nat → Expr
  | 0     => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

#eval natExpr 1
-- Lean.Expr.app
--   (Lean.Expr.const `Nat.succ [] (Expr.mkData 3403344051 (bi := Lean.BinderInfo.default)))
--   (Lean.Expr.const `Nat.zero [] (Expr.mkData 3114957063 (bi := Lean.BinderInfo.default)))
--   (Expr.mkData 3354277877 (approxDepth := 1) (bi := Lean.BinderInfo.default))
```

That's already a long expression for the natural number 1! Let's see what
`reduce : Expr → MetaM Expr` can do about it

```lean
#eval reduce $ natExpr 1
-- Lean.Expr.lit (Lean.Literal.natVal 1) (Expr.mkData 4289331193 (bi := Lean.BinderInfo.default))
```

The following example would yield an even longer expression, but `reduce`
can clean it up for us:

```lean
def sumExprM (n m : Nat) : MetaM Expr := do
  reduce $ mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]

#eval sumExprM 2 3 --Lean.Expr.lit (Lean.Literal.natVal 5) (Expr.mkData 1441793 (bi := Lean.BinderInfo.default))
```

We next construct a λ-expression for the function `double : Nat → Nat` given
by `double n = n + n`. To construct such an expression, a free variable `n` has
to be introduced, the expression defined in terms of this variable, and the
λ-expression should be constructed. 

The variable is introduced by passing the code using it as a _continuation_ to 
`withLocalDecl`. The arguments of `withLocalDecl` are:
* The name of the variable
* The _binder_ that determines whether it is explicit or not
* The type of the variable
* The function that turns an expression into something else (in our case, into
  another expression). This function does not need to be pure.

The λ-expression is constructed using `mkLambdaFVars`, with the first argument
being an array of free variables (just one in this case) with respect to which
we take λ. The second argument is the body of the λ-expression.

```lean
def doubleM : MetaM Expr :=
  withLocalDecl `n BinderInfo.default (mkConst ``Nat)
    fun n : Expr => mkLambdaFVars #[n] $ mkAppN (mkConst ``Nat.add) #[n, n]
```

Let's check if `doubleM` can indeed compute the expression for `n + n`

```lean
def appDoubleM (n : Nat) : MetaM Expr := do
  reduce $ mkApp (← doubleM) (natExpr n)

#eval appDoubleM 3 -- Lean.Expr.lit (Lean.Literal.natVal 6) (Expr.mkData 393219 (bi := Lean.BinderInfo.default))
```

A powerful feature of lean is its unifier. There is an easy way to use this
while meta-programming, namely the method `mkAppM` (and a similar method
`mkAppM'`). For example, we can construct an expression for the length of a list
using `mkAppM`. Recall that `List.length` has an implicit parameter
`α : Type u`. This is deduced by unification, as are universe levels.

```lean
def lenExprM (list: Expr) : MetaM Expr := do
  reduce $ ← mkAppM ``List.length #[list]
```

We test the unification in this definition.

```lean
def egList := [1, 3, 7, 8]

def egLenM : MetaM Expr := 
  lenExprM (mkConst ``egList)

#eval egLenM -- Lean.Expr.lit (Lean.Literal.natVal 4) (Expr.mkData 2490367 (bi := Lean.BinderInfo.default))
```

Analogous to the construction of λ-expressions, we can construct
∀-expressions (i.e., Π-expressions) for types. We simply replace
`mkLambdaFVars` with `mkForallFVars`.

A special case of Π-types are function types `A → B`. These can be constructed
using the function `mkArrow`. Another very useful meta-level function is `mkEq`,
which constructs equalities.

We illustrate all these, as well as the construction of a λ-expressions, by
constructing the proposition `∀ n: Nat, f n = f (n + 1)` as a function of `f`.
Formally this is `λ f, ∀ n, f n = f (n + 1)`. We break this into many steps to
illustrate the different ingredients.

First we build the expression for our proposition:

```lean
def propM : MetaM Expr := do
  let funcType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `f BinderInfo.default funcType fun f => do
  let feqn ← withLocalDecl `n BinderInfo.default (mkConst ``Nat) fun n => do
    let lhs := mkApp f n
    let rhs := mkApp f (← mkAppM ``Nat.succ #[n])
    let eqn ← mkEq lhs rhs
    mkForallFVars #[n] eqn
  mkLambdaFVars #[f] feqn
```

Now let's elaborate the expression into a term. This will be further explored
in the next chapter

```lean
elab "myProp" : term => propM

#check  myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n)
#reduce myProp Nat.succ -- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)

--fix: move the content below this line
--fix: part should go to the previous chapter and part to the next
```

As the code above was rather complicated, it is better to check it. A
convenient way to do this is to use an _elaborator_ to assign the expression to
a constant and then check it. We will explain elaborators in a future chapter.

One can construct _let-expressions_ in a manner similar to λ-expressions. We
use `withLetDecl` to introduce into the context a let declaration with given
name, type, value. We apply this to a _continuation_, which is a function with
variable corresponding to the one defined in the `let` statement. The
continuation should return an expression relative to the `let` declaration --
this is done using the `mkLetFVars` function.

```lean
elab "two!" : term => do
  let z := Lean.mkConst `Nat.zero
  let ty := Lean.mkConst `Nat
  withLetDecl `n ty z fun x => do
    let one ← mkAppM ``Nat.succ #[x]
    let two ← mkAppM ``Nat.add #[one, one]
    let e ← mkLetFVars #[x] two
    return e

#eval (two! : Nat) -- 2
```

## Meta variables

Meta-variables are variables that can be created and assigned to only at the
meta level, and not the object/term level. They are used principally as
placeholders, especially for goals. They can be assigned expressions in terms of
other meta variables. However, before being assigned to a pure (i.e., not meta)
definition, the assignments should be resolvable to a value not involving
meta-variables.

One way to create a meta-variable representing an expression is to use the
`mkFreshExprMVar` function. This function creates a meta-variable that can be
assigned an expression. One can optionally specify a type for the meta-variable.
In the example below, we create three meta-variables, `mvar1`, `mvar2`, and
`mvar3`, with `mvar1` and `mvar3` assigned type `Nat` and `mvar2` assigned the
type `Nat → Nat`.

We assign expressions to the meta-variables using the `assignExprMVar` function.
Like many functions dealing with meta-variables, this takes the id of the
meta-variable as an argument. Below we assign to `mvar1` the result of function
application of `mvar2` to `mvar3`. We then assign to `mvar2` the constant
expression `Nat.succ` and to `mvar3` the constant expression `Nat.zero`. Clearly
this means we have assigned `Nat.succ (Nat.zero)`, i.e., `1` to `mvar1`. We
return `mvar1` in the function `metaOneM`. We can see, using an elaborator, that
indeed when the expression `metaOneM` is assigned to a term, the result is `1`.

```lean
elab "one!" : term => do
  let zero := mkConst ``Nat.zero
  let mvar1 ← mkFreshExprMVar (some (mkConst ``Nat)) 
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat))
  let funcType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let mvar3 ← mkFreshExprMVar (some funcType)
  assignExprMVar mvar1.mvarId! (mkApp mvar3 mvar2)
  assignExprMVar mvar2.mvarId! zero 
  assignExprMVar mvar3.mvarId! (mkConst ``Nat.succ)
  return mvar1

#eval one! -- 1
```

## Matching on expressions

Often we wish to construct expressions depending on the nature of other
expressions. To do this, we can directly match given expressions using the
inductive nature of `Expr`. However, it is often more convenient to use helpers
that lean provides to recognize expressions of specific forms.

We consider one such example: given an equality type `lhs = rhs`, we construct
the type `rhs = lhs`. This is done by matching on the expression using
`Expr.eq?`, which returns `some (α, lhs, rhs)` if the expression is an equality,
with `α` the type of `lhs` (and `rhs`), and `none` otherwise.

Note that the elaborator for testing is a little more complicated than the
previous cases. Details of such elaborators will be discussed in a future
chapter.

```lean
def flipEquality (type: Expr): MetaM Expr := do
  match type.eq? with
  | some (α, lhs, rhs) =>
    mkEq rhs lhs
  | _ => throwError "can only flip equality types"

open Elab Term in
elab "flipEq!" ty:term : term => do
  let ty ← elabType ty
  let e ← flipEquality ty
  return e

#check flipEq! (5 = 3) -- 3 = 5 : Prop
```
