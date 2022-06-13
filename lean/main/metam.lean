/-
# `MetaM`

The Lean 4 metaprogramming API is organised around a small zoo of monads. The
four main ones are:

- `CoreM` gives access to the *environment*, i.e. the set of things that
  have been declared or imported at the current point in the program.
- `MetaM` gives access to the *metavariable context*, i.e. the set of
  metavariables that are currently declared and the values assigned to them (if
  any).
- `TermElabM` gives access to various information used during elaboration.
- `TacticM` gives access to the list of current goals.

These monads extend each other, so a `MetaM` operation also has access to the
environment and a `TermElabM` computation can use metavariables. There are also
other monads which do not neatly fit into this hierarchy, e.g. `CommandElabM`
extends `MetaM` but neither extends nor is extended by `TermElabM`.

This chapter demonstrates a number of useful operations in the `MetaM` monad.
`MetaM` is of particular importance because it allows us to give meaning to
every expression: the environment (from `CoreM`) gives meaning to constants like
`Nat.zero` or `List.map` and the metavariable context gives meaning to both
metavariables and local hypotheses. -/

import Lean

open Lean Lean.Expr Lean.Meta

/-!
## Computation

Computation is a core concept of dependent type theory. The terms `2`, `Nat.succ
1` and `1 + 1` are all "the same" in the sense that they compute the same value.
We call them *definitionally equal*. The problem with this, from a
metaprogramming perspective, is that definitionally equal terms may be
represented by entirely different expressions, but still our users would usually
expect that a tactic which works for `2` also works for `1 + 1`. So when we
write our tactics, we must do additional work to ensure that definitionally
equal terms are treated similarly.

### Full Normalisation

The simplest thing we can do with computation is to bring a term into normal
form. With some exceptions for numeric types, the normal form of a term `t` of
type `T` is a sequence of applications of `T`'s constructors. E.g. the normal
form of a list is a sequence of applications of `List.cons` and `List.nil`.

The function that normalises a term (i.e. brings it into normal form) is
`Lean.Meta.reduce` with type signature

```lean
reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr
```

We can use it like this:
-/

def someNumber : Nat := (· + 2) $ 3

#eval mkConst ``someNumber
-- Lean.Expr.const `someNumber [] (...)

#eval reduce (mkConst ``someNumber)
-- Lean.Expr.lit (Lean.Literal.natVal 5) (...)

/-!
Incidentally, this shows that the normal form of a term of type `Nat` is not
always an application of the constructors of `Nat`; it can also be a literal.
Also note that `#eval` can be used not only to evaluate a term, but also to
execute a `MetaM` program.

The optional arguments of `reduce` allow us to skip certain parts of an
expression. E.g. `reduce e (explicitOnly := true)` does not normalise any
implicit arguments in the expression `e`. This yields better performance: since
normal forms can be very big, it may be a good idea to skip parts of an
expression that the user is not going to see anyway.

The `#reduce` command is essentially an application of `reduce`:
-/

#reduce someNumber
-- 5

/-!
### Transparency

An ugly but important detail of Lean 4 metaprogramming is that any given
expression does not have a single normal form. Rather, it has a normal form up
to a given *transparency*.

A transparency is a value of `Lean.Meta.TransparencyMode`, an enumeration with
four values: `reducible`, `instances`, `default` and `all`. Any computation in
the `MetaM` has access to an ambient `TransparencyMode` which can be obtained
with `Lean.Meta.getTransparency`.

The current transparency determines which constants get unfolded during
normalisation, e.g. by `reduce`. (To unfold a constant means to replace it with
its definition.) The four settings unfold progressively more constants:

- `reducible`: unfold only constants tagged with the `@[reducible]` attribute.
  Note that `abbrev` is a shorthand for `@[reducible] def`.
- `instances`: unfold reducible constants and constants tagged with the
  `@[instance]` attribute. Again, the `instance` command is a shorthand for
  `@[instance] def`.
- `default`: unfold all constants except those tagged as `@[irreducible]`.
- `all`: unfold all constants, even those tagged as `@[irreducible]`.

The ambient transparency is usually `default`. To execute an operation with a
specific transparency, use `Lean.Meta.withTransparency`. There are also
shorthands for specific transparencies, e.g. `Lean.Meta.withReducible`.

Putting everything together for an example (where we use `Lean.Meta.ppExpr` to
pretty-print an expression): -/

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (mkConst c))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
Note that the instance `HAdd Nat Nat`, which is used for the `+` notation,
has also been unfolded.
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
Here the `Nat.add` function has been unfolded as well.
-/

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

/-!
The `#eval` commands illustrate that the same term, `reducibleDef`, can have a
different normal form for each transparency.

Why all this ceremony? Essentially for performance: if we allowed normalisation
to always unfold every constant, operations such as type class search would
become prohibitively expensive. The tradeoff is that we must choose the
appropriate transparency for each operation that involves normalisation.


### Weak Head Normalisation

Transparency addresses some of the performance issues with normalisation. But
even more important is to recognise that for many purposes, we don't need to
fully normalise terms at all. Suppose we are building a tactic that
automatically splits hypotheses of the form `P ∧ Q`. We might want this tactic
to recognise a hypothesis `h : X` if `X` is defined as `P ∧ Q ∧ R`. But if `P`
is additionally defined as `Y ∨ Z`, the specific `Y` and `Z` do not concern us.

This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

and `f` is either irreducible (at the current transparency) or is applied to too
few arguments. To conveniently check the WHNF of an expression, we define a
function `whnf'` which uses some advanced tech; don't worry about its
implementation for now.
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) (md := TransparencyMode.default) :
    TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

/-!
Now, here are some examples of expressions in WHNF.

Constructor applications are in WHNF (with some exceptions for numeric types):
-/

#eval whnf' `(List.cons 1 [])
-- [1]

/-!
The *arguments* of an application in WHNF may or may not be in WHNF themselves:
-/

#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

/-!
Functions applied to too few arguments are in WHNF:
-/

#eval whnf' `(Nat.add 1)
-- Nat.add 1

/-!
Applications of constants are in WHNF if the current transparency does not
allow us to unfold the constants:
-/

#eval withTransparency .reducible $ whnf' `(Nat.add 1 1)
-- Nat.add 1 1

/-!
Lambdas are in WHNF:
-/

#eval whnf' `(λ x : Nat => x)
-- fun x => x

/-!
Foralls are in WHNF:
-/

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

/-!
Sorts are in WHNF:
-/

#eval whnf' `(Type 3)
-- Type 3

/-!
Literals are in WHNF:
-/

#eval whnf' `((15 : Nat))
-- 15

/-!
Here are some more expressions in WHNF which are a bit tricky to test:

```lean
?x 0 1  -- Assuming the metavariable `?x` is unassigned, it is in WHNF.
h 0 1   -- Assuming `h` is a local hypothesis, it is in WHNF.
```

On the flipside, here are some expressions that are not in WHNF.

Functions applied to all their arguments are not in WHNF:
-/

#eval whnf' `(Nat.add 1 1)
-- `Nat.succ (Nat.add 1 0)`

/-!
`let` bindings are not in WHNF:
-/

#eval whnf' `(let x : Nat := 1; x)
-- `1`

/-!
Applications of lambdas are not in WHNF:
-/

#eval whnf' `((λ x : Nat => x) 1)
-- `1`

/-!
Even when a lambda is applied to too few arguments, the application is not in
WHNF:
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
And again some tricky examples:

```lean
?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`), its application is not
          in WHNF.
h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`), its
          application is not in WHNF.
```

Returning to the tactic that motivated this section, let us write a function
that matches a type of the form `P ∧ Q`, taking computation into account. WHNF
makes it easy:
-/

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnf e
  match e with
  | (.app (.app (.const ``And _ _) P _) Q _) => return some (P, Q)
  | _ => return none

/-
By using `whnf`, we ensure that if `e` evaluates to something of the form `P
∧ Q`, we'll notice. But at the same time, we don't perform any unnecessary
computation in `P` or `Q`.

However, our 'no unnecessary computation' mantra also means that if we want to
perform deeper matching on an expression, we need to use `whnf` multiple times.
Suppose we want to match a type of the form `P ∧ Q ∧ R`. The correct way to do
this uses `whnf` twice:
-/

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e ← whnf e
  match e with
  | (.app (.app (.const ``And _ _) P _) e' _) =>
    let e' ← whnf e'
    match e' with
    | (.app (.app (.const ``And _ _) Q _) R _) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-!
This sort of deep matching up to computation could be automated. But until
someone builds this automation, we have to figure out the necessary `whnf`s
ourselves.


### Definitional Equality

As mentioned, definitional equality is equality up to computation. Two
expressions `t` and `s` are definitionally equal or *defeq* (at the current
transparency) if their normal forms (at the current transparency) are equal.

To check whether two expressions are defeq, use `Lean.Meta.isDefEq` with type
signature

```lean
isDefEq : Expr → Expr → MetaM Bool
```

Even though definitional equality is defined in terms of normal forms, `isDefEq`
does not actually compute the normal forms of its arguments, which would be very
expensive. Instead, it tries to "match up" `t` and `s` using as few reductions
as possible. This is a necessarily heuristic endeavour and when the heuristics
misfire, `isDefEq` can become very expensive. In the worst case, it may have to
reduce `s` and `t` so often that they end up in normal form anyway. But usually
the heuristics are good and `isDefEq` is reasonably fast.


## Smart constructors for expressions

The `MetaM` monad provides even more smart constructors to help us build
expressions. The API also contains functions that help us explore certain
expressions more easily. In this chapter we will visit some of those.

A typical example of an expression we work with is that for the _goal_ of a tactic. This is an expression that represents a type. The tactic may attempt to find an expression that is of that type.
If it succeeds we can then use the expression to solve the goal. However, in `MetaM` we do not have _goals_, so in this chapter we illustrate the smart methods used to manipulate expressions.

Before manipulating expressions, we look at some examples of expressions.
To do this, let's recap the definition of `natExpr`, which gives expressions for natural numbers. -/

def natExpr : Nat → Expr
  | 0     => mkConst ``Nat.zero
  | n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)

#eval natExpr 1
-- Lean.Expr.app
--   (Lean.Expr.const `Nat.succ [] (Expr.mkData 3403344051 (bi := Lean.BinderInfo.default)))
--   (Lean.Expr.const `Nat.zero [] (Expr.mkData 3114957063 (bi := Lean.BinderInfo.default)))
--   (Expr.mkData 3354277877 (approxDepth := 1) (bi := Lean.BinderInfo.default))

/-
That's already a long expression for the natural number 1! `reduce` can simplify
it:
-/

#eval reduce $ natExpr 1
-- Lean.Expr.lit (Lean.Literal.natVal 1) (Expr.mkData 4289331193 (bi := Lean.BinderInfo.default))

/-! One of the first ways to construct expressions is by function application to form the expression for `f a` given expressions for `f` and `a`. One uses various methods provided by lean 4 to do this. It is generally not a good idea to try to directly define the expression as there is associated metadata.

The simple methods for constructing expressions by function application are `mkApp` and `mkAppN`. These take care of the metadata, but do not attempt to unify, for example. The `mkAppN` function takes a function and an array of arguments. The name ending with `N` here (and elsewhere) is to indicate that we (in general) have multiple (`N`) arguments. On the other hand `mkApp` applies a function to a single argument.

The following example illustrates constructing examples using `mkAppN`. This
would yield an even longer expression than the previous example, but we again
use `reduce` to simplify it:
-/

def sumExprM (n m : Nat) : MetaM Expr := do
  reduce $ mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]

#eval sumExprM 2 3 --Lean.Expr.lit (Lean.Literal.natVal 5) (Expr.mkData 1441793 (bi := Lean.BinderInfo.default))

/-! Note that the _function_ to be applied is a constant, so has an expression of the form `mkConst name`. The name was given preceded by double-backticks. This means that lean resolves this to a global name, and gives an error if it cannot be resolved. A name preceded by a single backtick is a literal name.
-/

/-! Besides function application, we would like to construct expressions using λ-expressions. 
We next illustrate how to do this by constructing a λ-expression for the function `double : Nat → Nat` given by `double n = n + n`. 

To construct such an expression, we _introduce_ a free variable `n`, we define an expression in terms of this variable, and finally construct the λ-expression. 

Introducing the free variable in this context is done indirectly. Roughly speaking the following happens. 

* A new _context_ is constructed where the free variable is defined. 
* We have code _within_ the context that uses the free variable; to avoid name collisions, this is a function of the expression for the free variable just introduced.
* There is a smart method that allows us to construct a λ-expression with respect to the free variable we have just created, taking care of matching names, hygeine etc.
* Our function working within the new context (called a _continuation_) can thus return an expression that does not depend on the free variable.

More formally, the variable is introduced by passing the code using it as a _continuation_ to 
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

/- We used `n` in two independent ways in the above expression. The first is simply as 
a name to be used in the body of the λ-expression. The second is as the name of the expression for the free variable created. We could have replaced one of them, or even used `Name.anonymous` for the first occurence.

Let's check if `doubleM` can indeed compute the expression for `n + n` -/

def appDoubleM (n : Nat) : MetaM Expr := do
  reduce $ mkApp (← doubleM) (natExpr n)

#eval appDoubleM 3 -- Lean.Expr.lit (Lean.Literal.natVal 6) (Expr.mkData 393219 (bi := Lean.BinderInfo.default))

/- 
Observe that in the expression for double, we used the function `Nat.add` and so could specify all its arguments quite easily. However, the expression `n + n` actually resolves to an application of `HAdd.add` with many implicit parameters -- three associated types as well as a typeclass. When working with lean (at the non-meta level) we depend on the unifier and typeclass inference to fill these arguments for us.

Fortunately we can use unification at the meta-level too, using the method `mkAppM` (and a similar method `mkAppM'`). The method name ending in `M` indicates that it is _monadic_ - in this case returning `MetaM Expr` rather than `Expr`. As one may expect, this usually is because some magic is happening for this to be necessary.

For example, we can construct an expression for the length of a list
using `mkAppM`. Recall that `List.length` has an implicit parameter
`α : Type u`. This is deduced by unification, as are universe levels. -/

def lenExprM (list: Expr) : MetaM Expr := do
  reduce $ ← mkAppM ``List.length #[list]

/- We test the unification in this definition. -/

def egList := [1, 3, 7, 8]


def egLenM : MetaM Expr := 
  lenExprM (mkConst ``egList)

#eval egLenM -- Lean.Expr.lit (Lean.Literal.natVal 4) (Expr.mkData 2490367 (bi := Lean.BinderInfo.default))

/-! We next sketch some more methods for constructing expressions.

Analogous to the construction of λ-expressions, we can construct
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
## Metavariables

Metavariables are variables that can be created and assigned to only at the
meta level, and not the object/term level. They are used principally as
placeholders, especially for goals. They can be assigned expressions in terms of
other metavariables. However, before being assigned to a pure (i.e., not meta)
definition, the assignments should be resolvable to a value not involving
metavariables.

One way to create a metavariable representing an expression is to use the
`mkFreshExprMVar` function. This function creates a metavariable that can be
assigned an expression. One can optionally specify a type for the metavariable.
In the example below, we create three metavariables, `mvar1`, `mvar2`, and
`mvar3`, with `mvar1` and `mvar3` assigned type `Nat` and `mvar2` assigned the
type `Nat → Nat`.

We assign expressions to the metavariables using the `assignExprMVar` function.
Like many functions dealing with metavariables, this takes the id of the
metavariable as an argument. Below we assign to `mvar1` the result of function
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
