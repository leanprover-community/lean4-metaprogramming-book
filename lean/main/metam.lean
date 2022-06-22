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
## Metavariables

### Overview

The 'Meta' in `MetaM` refers to metavariables, so we should talk about these
first. Lean users do not usually interact much with metavariables -- at least
not consciously -- but they are used all over the place in metaprograms. There
are two ways to view them: as holes in an expression or as goals.

Take the goal perspective first. When we prove things in Lean, we always operate
on goals, such as

```lean
n m : Nat
⊢ n + m = m + n
```

These goals are internally represented by metavariables. Accordingly, each
metavariable has a *local context* containing hypotheses (here `[n : Nat, m :
Nat]`) and a *target type* (here `n + m = m + n`). Metavariables also have a
unique name, say `m`, and we usually render them as `?m`.

To close a goal, we must give an expression `e` of the target type. The
expression may contain fvars from the metavariable's local context, but no
others. Internally, closing a goal in this way corresponds to *assigning* the
metavariable; we write `?m := e` for this assignment.

The second, complementary view of metavariables is that they represent holes
in an expression. For instance, an application of `Eq.trans` may generate two
goals which look like this:

```lean
n m : Nat
⊢ n = ?x

n m : Nat
⊢ ?x = m
```

Here `?x` is another metavariable -- a hole in the target types of both goals,
to be filled in later during the proof. The type of `?x` is `Nat` and its local
context is `[n : Nat, m : Nat]`. Now, if we solve the first goal by reflexivity,
then `?x` must be `n`, so we assign `?x := n`. Crucially, this also affects the
second goal: it is "updated" (not really, as we will see) to have target `n =
m`. The metavariable `?x` represents the same expression everywhere it occurs.


### Tactic Communication via Metavariables

Tactics use metavariables to communicate the current goals. To see how, consider
this simple (and slightly artificial) proof:
-/

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

/-!
After we enter tactic mode, our ultimate goal is to generate an expression of
type `f (f a) = a` which may involve the hypotheses `α`, `a`, `f` and `h`. So
Lean generates a metavariable `?m1` with target `f (f a) = a` and a local
context containing these hypotheses. This metavariable is passed to the first
`apply` tactic as the current goal.

The `apply` tactic then tries to apply `Eq.trans` and succeeds, generating three
new metavariables:

```lean
...
⊢ f (f a) = ?b

...
⊢ ?b = a

...
⊢ α
```

Call these metavariables `?m2`, `?m3` and `?b`. The last one, `?b`, stands for
the intermediate element of the transitivity proof and occurs in `?m2` and
`?m3`. The local contexts of all metavariables in this proof are the same, so
we omit them.

Having created these metavariables, `apply` assigns

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
```

and reports that `?m2`, `?m3` and `b` are now the current goals.

At this point the second `apply` tactic takes over. It receives `?m2` as the
current goal and applies `h` to it. This succeeds and the tactic assigns `?m2 :=
h (f a)`. This assignment implies that `?b` must be `f a`, so the tactic also
assigns `?b := f a`. Assigned metavariables are not considered open goals, so
the only goal that remains is `?m3`.

Now the third `apply` comes in. Since `?b` has been assigned, the target of
`?m3` is now `f (f a) = a`. Again, the application of `h` succeeds and the
tactic assigns `?m3 := h a`.

At this point, all metavariables are assigned as follows:

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
?m2 := h (f a)
?m3 := h a
?b  := f a
```

Exiting the `by` block, Lean constructs the final proof term by taking the
assignment of `?m1` and replacing each metavariable with its assignment. This
yields

```lean
@Eq.trans α (f (f a)) (f a) a (h (f a)) (h a)
```

The example also shows how the two views of metavariables -- as holes in an
expression or as goals -- are related: the goals we get are holes in the final
proof term.


### Basic Operations

Let us make these concepts concrete. When we operate in the `MetaM` monad, we
have read-write access to a `MetavarContext` structure containing information
about the currently declared metavariables. Each metavariable is identified by
an `MVarId` (a unique `Name`). To create a new metavariable, we use
`Lean.Meta.mkFreshExprMVar` with type

```lean
mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural)
    (userName := Name.anonymous) : MetaM Expr
```

Its arguments are:

- `type?`: the target type of the new metavariable. If `none`, the target type
  is `Sort ?u`, where `?u` is a universe level metavariable. (This is a special
  class of metavariables for universe levels, distinct from the expression
  metavariables which we have been calling simply "metavariables".)
- `kind`: the metavariable kind. See the [Metavariable Kinds
  section](#metavariable-kinds) (but the default is usually correct).
- `userName`: the new metavariable's user-facing name. This is what gets printed
  when the metavariable appears in a goal. Unlike the `MVarId`, this name does
  not need to be unique.

The returned `Expr` is always a metavariable. We can use `Lean.Expr.mvarId!` to
extract the `MVarId`, which is guaranteed to be unique. (Arguably
`mkFreshExprMVar` should just return the `MVarId`.)

The local context of the new metavariable is inherited from the current local
context, more about which in the next section. If you want to give a different
local context, use `Lean.Meta.mkFreshExprMVarAt`.

Metavariables are initially unassigned. To assign them, use
`Lean.Meta.assignExprMVar` with type

```lean
assignExprMVar (mvarId : MVarId) (val : Expr) : MetaM Unit
```

This updates the `MetavarContext` with the assignment `?mvarId := val`. You must
make sure that `mvarId` is not assigned yet (or that the old assignment is
definitionally equal to the new assignment). You must also make sure that the
assigned value, `val`, has the right type. This means (a) that `val` must have
the target type of `mvarId` and (b) that `val` must only contain fvars from the
local context of `mvarId`.

To get information about a declared metavariable, use `Lean.Meta.getMVarDecl`.
Given an `MVarId`, this returns a `MetavarDecl` structure. (If no metavariable
with the given `MVarId` is declared, the function throws an exception.) The
`MetavarDecl` contains information about the metavariable, e.g. its type, local
context and user-facing name. This function has some convenient variants, such
as `Lean.Meta.getMVarType`.

To get the current assignment of a metavariable (if any), use
`Lean.Meta.getExprMVarAssignment?`. To check whether a metavariable is assigned,
use `Lean.Meta.isExprMVarAssigned`. However, these functions are relatively
rarely used in tactic code because we usually prefer a more powerful operation:
`Lean.Meta.instantiateMVars` with type

```lean
instantiateMVars : Expr → MetaM Expr
```

Given an expression `e`, `instantiateMVars` replaces any assigned metavariable
`?m` in `e` with its assigned value. Unassigned metavariables remain as they
are.

This operation should be used liberally. When we assign a metavariable, existing
expressions containing this metavariable are not immediately updated. This is a
problem when, for example, we match on an expression to check whether it is an
equation. Without `instantiateMVars`, we might miss the fact that the expression
`?m`, where `?m` happens to be assigned to `0 = n`, represents an equation. In
other words, `instantiateMVars` brings our expressions up to date with the
current metavariable state.

Instantiating metavariables requires a full traversal of the input expression,
so it can be somewhat expensive. But if the input expression does not contain
any metavariables, `instantiateMVars` is essentially free. Since this is the
common case, liberal use of `instantiateMVars` is fine in most situations.

Before we go on, here is a synthetic example demonstrating how the basic
metavariable operations are used. More natural examples appear in the following
sections.
-/

#eval show MetaM Unit from do
  -- Create two fresh metavariables of type `Nat`.
  let mvar1 ← mkFreshExprMVar (mkConst ``Nat) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (mkConst ``Nat) (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar3 ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkConst ``Nat))
    (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  assignExprMVar mvar1.mvarId! (mkApp mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  assignExprMVar mvar2.mvarId! (mkConst ``Nat.zero)
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  assignExprMVar mvar3.mvarId! (mkConst ``Nat.succ)
  IO.println "After assigning mvar3:"
  printMVars
-- Initially, all metavariables are unassigned:
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar1:
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar2:
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- After assigning mvar3:
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ


/-!
### Local Contexts

Consider the expression `e` which refers to the free variable with unique name
`h`:

```lean
e := mkFVar (FVarId.mk `h)
```

What is the type of this expression? The answer depends on the local context in
which `e` is interpreted. One local context may declare that `h` is a local
hypothesis of type `Nat`; another local context may declare that `h` is a local
definition with value `List.map`.

Thus, expressions are only meaningful if they are interpreted in the local
context for which they were intended. And as we saw, each metavariable has its
own local context. So in principle, functions which manipulate expressions
should have an additional `MVarId` argument specifying the goal in which the
expression should be interpreted.

That would be cumbersome, so Lean goes a slightly different route. In `MetaM`,
we always have access to an ambient `LocalContext`, obtained with `Lean.getLCtx`
of type

```lean
getLCtx : MetaM LocalContext -- real type is more general
```

All operations involving fvars use this ambient local context.


The downside of this setup is that we always need to update the ambient local
context to match the goal we are currently working on. To do this, we use
`Lean.Meta.withMVarContext` of type (again specialised)

```lean
withMVarContext (mvarId : MVarId) (c : MetaM α) : MetaM α
```

This function takes a metavariable `mvarId` and a `MetaM` computation `c` and
executes `c` with the ambient context set to the local context of `mvarId`. A
typical use case looks like this:

```lean
def someTactic (mvarId : MVarId) ... : ... :=
  withMVarContext mvarId do
    ...
```

The tactic receives the current goal as the metavariable `mvarId` and
immediately sets the current local context. Any operations within the `do` block
then use the local context of `mvarId`.

Once we have the local context properly set, we can manipulate fvars. Like
metavariables, fvars are identified by an `FVarId` (a unique `Name`). Basic
operations include:

- `Lean.Meta.getLocalDecl : FVarId → MetaM LocalDecl` retrieves the declaration
  of a local hypothesis. As with metavariables, a `LocalDecl` contains all
  information pertaining to the local hypothesis, e.g. its type and its
  user-facing name.
- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` retrieves the
  declaration of the local hypothesis with the given user-facing name. If there
  are multiple such hypotheses, the bottommost one is returned. If there is
  none, an exception is thrown.

We can also iterate over all hypotheses in the local context, using the `ForIn`
instance of `LocalContext`. A typical pattern is this:

```lean
for ldecl in ← getLCtx do
  if ldecl.isAuxDecl then
    continue
  -- do something with the ldecl
```

The loop iterates over every `LocalDecl` in the context. The `isAuxDecl` check
skips so-called auxiliary declarations. These are local hypotheses which are
inserted by the equation compiler, are invisible to the user and must be ignored
by tactics.

At this point, we can build the `MetaM` part of an `assumption` tactic:
-/

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Check that `mvarId` is not already assigned.
  checkNotAssigned mvarId `myAssumption
  -- Use the local context of `mvarId`.
  withMVarContext mvarId do
    -- The target is the type of `mvarId`.
    let target ← getMVarType mvarId
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an auxiliary declaration, skip it.
      if ldecl.isAuxDecl then
        continue
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        assignExprMVar mvarId ldecl.toExpr
        -- Stop and return true.
        return true
    -- If we have not found any suitable local hypothesis, return false.
    return false

/-!
The `myAssumption` tactic contains three functions we have not seen before:

- `Lean.Meta.checkNotAssigned` checks that a metavariable is not already
  assigned. The 'myAssumption' argument is the name of the current tactic. It is
  used to generate a nicer error message.
- `Lean.Meta.isDefEq` checks whether two definitions are definitionally equal.
  See the [Definitional Equality section](#definitional-equality).
- `Lean.LocalDecl.toExpr` is a helper function which constructs the expression
  corresponding to a local hypothesis.


### Delayed Assignments

The above discussion of metavariable assignment contains a lie by omission:
there are actually two ways to assign a metavariable. We have seen the regular
way; the other way is called a *delayed assignment*.

We do not discuss delayed assignments in any detail here since they are rarely
useful for tactic writing. If you want to learn more about them, see the
comments in `MetavarContext.lean` in the Lean standard library. But they create
two complications which you should be aware of.

First, delayed assignments make `isExprMVarAssigned` and
`getExprMVarAssignment?` medium-calibre footguns. These functions only check for
regular assignments, so you may need to use `Lean.Meta.isDelayedAssigned` and
`Lean.Meta.getDelayedAssignment?` as well.

Second, delayed assignments break an intuitive invariant. You may have assumed
that any metavariable which remains in the output of `instantiateMVars` is
unassigned, since the assigned metavariables have been substituted. But delayed
metavariables can only be substituted once their assigned value contains no
unassigned metavariables. So delayed-assigned metavariables can appear in an
expression even after `instantiateMVars`.


### Metavariable Depth

Metavariable depth is also a niche feature, but one that is occasionally useful.
Any metavariable has a *depth* (a natural number), and a `MetavarContext` has a
corresponding depth as well. Lean only assigns a metavariable if its depth is
equal to the depth of the current `MetavarContext`. Newly created metavariables
inherit the `MetavarContext`'s depth, so by default every metavariable is
assignable.

This setup can be used when a tactic needs some temporary metavariables and also
needs to make sure that other, non-temporary metavariables will not be assigned.
To ensure this, the tactic proceeds as follows:

1. Save the current `MetavarContext`.
2. Increase the depth of the `MetavarContext`.
3. Perform whatever computation is necessary, possibly creating and assigning
   metavariables. Newly created metavariables are at the current depth of the
   `MetavarContext` and so can be assigned. Old metavariables are at a lower
   depth, so cannot be assigned.
4. Restore the saved `MetavarContext`, thereby erasing all the temporary
   metavariables and resetting the `MetavarContext` depth.

This pattern is encapsulated in `Lean.Meta.withNewMCtxDepth`.


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

/-!
Note that with `TransparencyMode.instances`, an instance of `HAdd Nat Nat`,
which is used for the `+` notation, has also been unfolded:
-/

-- the instance to be unfolded, `@instHAdd Nat instAddNat`,
-- can be seen when we pretty-print the implicit arguments below:
set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1
set_option pp.explicit false

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
With `TransparencyMode.default`, the `Nat.add` function is unfolded as well:
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
And with `TransparencyMode.all`, we're finally able to unfold `irreducibleDef`:
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
automatically splits hypotheses of the type `P ∧ Q`. We might want this tactic
to recognise a hypothesis `h : X` if `X` reduces to `P ∧ Q`. But if `P`
additionally reduces to `Y ∨ Z`, the specific `Y` and `Z` do not concern us:
it's unnecessary extra computation that does not need to happen.

This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

and `f` cannot be reduced (at the current transparency). To conveniently check
the WHNF of an expression, we define a function `whnf'` which uses some advanced
tech; don't worry about its implementation for now.
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
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
Applications of constants are in WHNF if the current transparency does not
allow us to unfold the constants:
-/

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

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

Applications of constants are not in WHNF:
-/

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x

/-!
Applications of lambdas are not in WHNF:
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
`let` bindings are not in WHNF:
-/

#eval whnf' `(let x : Nat := 1; x)
-- 1

/-!
And again some tricky examples:

```lean
?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`), its application is not
          in WHNF.
h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`), its
          application is not in WHNF.
```

Returning to the tactic that motivated this section, let us write a function
that matches a type of the form `P ∧ Q`, avoiding extra computation. WHNF
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

If expressions `t` and `u` contain assignable metavariables, `isDefEq` may
assign these metavariables to make `t` defeq to `u`. We also say that `isDefEq`
*unifies* `t` and `u`; unification queries are sometimes written `t =?= u`. For
instance, the unification `List ?m =?= List Nat` succeeds and assigns `?m :=
Nat`. The unification `Nat.succ ?m =?= n + 1` succeeds and assigns `?m := n`.
The unification `?m₁ + ?m₂ + ?m₃ =?= m + n - k` fails and no metavariables
are assigned (even though there is a 'partial match' between the expressions).

Whether `isDefEq` considers a metavariable assignable is determined by two
factors:

1. The metavariable's depth must be equal to the current `MetavarContext` depth.
   See the [Metavariable Depth section](#metavariable-depth).
2. Each metavariable has a *kind* (a value of type `MetavarKind`) whose sole
   purpose is to modify the behaviour of `isDefEq`. Possible kinds are:
   - Natural: `isDefEq` may freely assign the metavariable. This is the default.
   - Synthetic: `isDefEq` may assign the metavariable, but avoids doing so if
     possible. For example, suppose `?n` is a natural metavariable and `?s` is a
     synthetic metavariable. When faced with the unification problem
     `?s =?= ?n`, `isDefEq` assigns `?n` rather than `?s`.
   - Synthetic opaque: `isDefEq` never assigns the metavariable.


## Smart constructors for expressions

The `MetaM` monad provides even more smart constructors to help us build
expressions. The API also contains functions that help us explore certain
expressions more easily. In this chapter we will visit some of those.

A typical example of an expression we work with is that of the _goal_ of a tactic. This is an expression that represents a type. The tactic may attempt to find an expression that is of that type.
If it succeeds, we can then use the expression to solve the goal. However, in `MetaM` we do not have _goals_, so in this chapter we illustrate the smart methods used to manipulate expressions.

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

/-! One of the first ways to construct expressions is by function application, that is, to form the expression for `f a` given expressions for `f` and `a`. One uses various methods provided by Lean 4 to do this. It is generally not a good idea to try to directly define the expression, as there is associated metadata that needs to be included which is difficult to construct manually.

The simple methods for constructing expressions by function application are `mkApp` and `mkAppN`. These take care of the metadata, but do not attempt to unify, for example. The `mkAppN` function takes a function and an array of arguments. The name ending with `N` here (and elsewhere) is to indicate that we (in general) have multiple (`N`) arguments. On the other hand `mkApp` applies a function to a single argument.

The following example illustrates constructing examples using `mkAppN`. This
would yield an even longer expression than the previous example, but we again
use `reduce` to simplify it:
-/

def sumExprM (n m : Nat) : MetaM Expr := do
  reduce $ mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]

#eval sumExprM 2 3 --Lean.Expr.lit (Lean.Literal.natVal 5) (Expr.mkData 1441793 (bi := Lean.BinderInfo.default))

/-! Note that the _function_ to be applied is a constant, and so has an expression of the form `mkConst name`. The name was given preceded by double-backticks. This means that Lean resolves this to a global name, and gives an error if it cannot be resolved. A name preceded by a single backtick is a literal name.
-/

/-! Besides function application, we would like to construct expressions using λ-expressions. 
We next illustrate how to do this by constructing a λ-expression for the function `double : Nat → Nat` given by `double n = n + n`. 

To construct such an expression, we _introduce_ a free variable `n`, define an expression in terms of this variable, and finally construct the λ-expression. 

Introducing the free variable in this context is done indirectly. Roughly speaking, the following happens:

* A new _context_ is constructed where the free variable is defined. 
* We have code _within_ the context that uses the free variable; to avoid name collisions, this is a function of the expression for the free variable just introduced.
* There is a smart method that allows us to construct a λ-expression with respect to the free variable we have just created, taking care of matching names, hygeine etc.
* Our function working within the new context (called a _continuation_) can thus return an expression that does not depend on the free variable.

More formally, the variable is introduced by passing the code using it as a _continuation_ to 
`withLocalDecl`. The arguments of `withLocalDecl` are:

* The name of the variable
* The _binder info_ that determines whether it is explicit or not
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
a name to be used in the body of the λ-expression (at the non-meta level). The second is as the name of the expression for the free variable created (at the meta level). We could have replaced one of them, or even used `Name.anonymous` for the first occurrence.

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

def lenExprM (list : Expr) : MetaM Expr := do
  reduce $ ← mkAppM ``List.length #[list]

/- We test the unification in this definition: -/

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
what we did more easily. This will be further explored in the "elaboration" chapter. -/

elab "myProp" : term => propM

#check  myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce myProp -- fun f => ∀ (n : Nat), f n = f (Nat.succ n)
#reduce myProp Nat.succ -- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)

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
