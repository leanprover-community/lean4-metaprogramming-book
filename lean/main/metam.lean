/-
# `MetaM`

## Smart constructors for expressions

The `MetaM` monad provides even more smart constructors to help us build
expressions. The API also contains functions that help us explore certain
expressions more easily. In this chapter we will visit some of those.

But first, let's recap the definition of `natExpr` -/

import Lean

open Lean Meta

def natExpr : Nat → Expr
  | 0     => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

#eval natExpr 1
-- Lean.Expr.app
--   (Lean.Expr.const `Nat.succ [] (Expr.mkData 3403344051 (bi := Lean.BinderInfo.default)))
--   (Lean.Expr.const `Nat.zero [] (Expr.mkData 3114957063 (bi := Lean.BinderInfo.default)))
--   (Expr.mkData 3354277877 (approxDepth := 1) (bi := Lean.BinderInfo.default))

/- That's already a long expression for the natural number 1! Let's see what
`reduce : Expr → MetaM Expr` can do about it-/

#eval reduce $ natExpr 1
-- Lean.Expr.lit (Lean.Literal.natVal 1) (Expr.mkData 4289331193 (bi := Lean.BinderInfo.default))

/- The following example would yield an even longer expression, but `reduce`
can clean it up for us: -/

def sumExprM (n m : Nat) : MetaM Expr := do
  reduce $ mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]

#eval sumExprM 2 3 --Lean.Expr.lit (Lean.Literal.natVal 5) (Expr.mkData 1441793 (bi := Lean.BinderInfo.default))

/-! We next construct a λ-expression for the function `double : Nat → Nat` given
by `double n = n + n`. To construct such an expression, we introduce a free
variable `n`, we define an expression in terms of this variable, and we construct
the λ-expression.

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
-/

def doubleM : MetaM Expr :=
  withLocalDecl `n BinderInfo.default (mkConst ``Nat)
    fun n : Expr => mkLambdaFVars #[n] $ mkAppN (mkConst ``Nat.add) #[n, n] 

/- Let's check if `doubleM` can indeed compute the expression for `n + n` -/

def appDoubleM (n : Nat) : MetaM Expr := do
  reduce $ mkApp (← doubleM) (natExpr n)

#eval appDoubleM 3 -- Lean.Expr.lit (Lean.Literal.natVal 6) (Expr.mkData 393219 (bi := Lean.BinderInfo.default))

/- A powerful feature of lean is its unifier. There is an easy way to use this
while meta-programming, namely the method `mkAppM` (and a similar method
`mkAppM'`). For example, we can construct an expression for the length of a list
using `mkAppM`. Recall that `List.length` has an implicit parameter
`α : Type u`. This is deduced by unification, as are universe levels. -/

def lenExprM (list: Expr) : MetaM Expr := do
  reduce $ ← mkAppM ``List.length #[list]

/- We test the unification in this definition. -/

def egList := [1, 3, 7, 8]

def egLenM : MetaM Expr := 
  lenExprM (mkConst ``egList)

#eval egLenM -- Lean.Expr.lit (Lean.Literal.natVal 4) (Expr.mkData 2490367 (bi := Lean.BinderInfo.default))

/-! Analogous to the construction of λ-expressions, we can construct
∀-expressions (i.e., Π-expressions) for types. We simply replace
`mkLambdaFVars` with `mkForallFVars`.

A special case of Π-types are function types `A → B`. These can be constructed
using the function `mkArrow`. Another very useful meta-level function is `mkEq`,
which constructs equalities.

We illustrate all these, as well as the construction of a λ-expression, by
constructing the proposition `∀ n: Nat, f n = f (n + 1)` as a function of `f`.
Formally this is `λ f, ∀ n, f n = f (n + 1)`. We break this into many steps to
illustrate the different ingredients.

First we build the expression for our proposition:
-/

def propM : MetaM Expr := do
  let funcType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `f BinderInfo.default funcType fun f => do
  let feqn ← withLocalDecl `n BinderInfo.default (mkConst ``Nat) fun n => do
    let lhs := mkApp f n
    let rhs := mkApp f (← mkAppM ``Nat.succ #[n])
    let eqn ← mkEq lhs rhs
    mkForallFVars #[n] eqn
  mkLambdaFVars #[f] feqn

/- Now let's elaborate the expression into a term so we can see the result of
what we did more easily. This will be further explored in the next chapter -/

elab "myProp" : term => propM

#check  myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n)
#reduce myProp Nat.succ -- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)

/-!
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
-/

def oneMetaVar : MetaM Expr := do
  let zero := mkConst ``Nat.zero
  let mvar1 ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat))
  let funcType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
  let mvar3 ← mkFreshExprMVar (some funcType)
  IO.println "the initial state of each metavariable:"
  IO.println $ ← instantiateMVars mvar1
  IO.println $ ← instantiateMVars mvar2
  IO.println $ ← instantiateMVars mvar3
  IO.println "--------------------------------"
  assignExprMVar mvar1.mvarId! (mkApp mvar3 mvar2)
  IO.println "after turning `mvar1` into an application:"
  IO.println $ ← instantiateMVars mvar1
  IO.println $ ← instantiateMVars mvar2
  IO.println $ ← instantiateMVars mvar3
  IO.println "--------------------------------"
  assignExprMVar mvar2.mvarId! zero
  IO.println "after turning the application argument into `Nat.zero`:"
  IO.println $ ← instantiateMVars mvar1
  IO.println $ ← instantiateMVars mvar2
  IO.println $ ← instantiateMVars mvar3
  IO.println "--------------------------------"
  assignExprMVar mvar3.mvarId! (mkConst ``Nat.succ)
  IO.println "after turning the application function into `Nat.succ`:"
  IO.println $ ← instantiateMVars mvar1
  IO.println $ ← instantiateMVars mvar2
  IO.println $ ← instantiateMVars mvar3
  IO.println "--------------------------------"
  return mvar1

elab "one!" : term => oneMetaVar

#eval one! -- 1
-- the initial state of each metavariable:
-- ?_uniq.3411
-- ?_uniq.3412
-- ?_uniq.3413
-- --------------------------------
-- after turning `mvar1` into an application:
-- ?_uniq.3413 ?_uniq.3412
-- ?_uniq.3412
-- ?_uniq.3413
-- --------------------------------
-- after turning the application argument into `Nat.zero`:
-- ?_uniq.3413 Nat.zero
-- Nat.zero
-- ?_uniq.3413
-- --------------------------------
-- after turning the application function into `Nat.succ`:
-- Nat.succ Nat.zero
-- Nat.zero
-- Nat.succ
-- --------------------------------

/-!
## Telescopes

Before going further, let's take a step back and think about the `Expr.lam`
constructor:

```lean
Expr.lam : Name → Expr → Expr → Data → Expr
```

The first `Expr` is the type of the function's input and the second is its body.
Then we ask ourselves: how do we build a function with multiple input variables?
Well, we use the same constructor multiple times, one for each input variable.

As an example, let's see an approximation of how we'd build the function
`fun (x : Nat) (y : Nat) => x + y`:

```lean
Expr.lam `x (mkConst ``Nat) (Expr.lam `y (mkConst ``Nat) b) d') d
```

It's done by nesting a new `Expr.lam` as the body of another `Expr.lam`. Thus,
if we wanted to, say, perform a computation that involves all the input types of
a function as well as its body, we would have to unfold the expression
recursively until the last nested `Expr.lam` just to gather everything we need
to do what we want. And that's when `lambdaTelescope` comes into play.

```lean
def lambdaTelescope (e : Expr) (k : Array Expr → Expr → m α) : m α
```

It makes it easier for us to do our computation with the data that we need. All
we need to do is provide a `k` function, whose first argument is an array of
input types and the second argument is the function body.

There are multiple telescopes in the API and we don't intend to be exhaustive
here. Something to note is that `m` is not necessarily the `MetaM` monad, but we
are covering this subject here because telescopes are defined in `Lean.Meta` and
also because we are already in `MetaM` when we want to use more powerful tools
to deal with expressions. -/
