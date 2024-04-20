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

and reports that `?m2`, `?m3` and `?b` are now the current goals.

At this point the second `apply` tactic takes over. It receives `?m2` as the
current goal and applies `h` to it. This succeeds and the tactic assigns `?m2 :=
h (f a)`. This assignment implies that `?b` must be `f a`, so the tactic also
assigns `?b := f a`. Assigned metavariables are not considered open goals, so
the only goal that remains is `?m3`.

Now the third `apply` comes in. Since `?b` has been assigned, the target of
`?m3` is now `f a = a`. Again, the application of `h` succeeds and the
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
`Lean.MVarId.assign` with type

```lean
assign (mvarId : MVarId) (val : Expr) : MetaM Unit
```

This updates the `MetavarContext` with the assignment `?mvarId := val`. You must
make sure that `mvarId` is not assigned yet (or that the old assignment is
definitionally equal to the new assignment). You must also make sure that the
assigned value, `val`, has the right type. This means (a) that `val` must have
the target type of `mvarId` and (b) that `val` must only contain fvars from the
local context of `mvarId`.

If you `#check Lean.MVarId.assign`, you will see that its real type is more
general than the one we showed above: it works in any monad that has access to a
`MetavarContext`. But `MetaM` is by far the most important such monad, so in
this chapter, we specialise the types of `assign` and similar functions.

To get information about a declared metavariable, use `Lean.MVarId.getDecl`.
Given an `MVarId`, this returns a `MetavarDecl` structure. (If no metavariable
with the given `MVarId` is declared, the function throws an exception.) The
`MetavarDecl` contains information about the metavariable, e.g. its type, local
context and user-facing name. This function has some convenient variants, such
as `Lean.MVarId.getType`.

To get the current assignment of a metavariable (if any), use
`Lean.getExprMVarAssignment?`. To check whether a metavariable is assigned, use
`Lean.MVarId.isAssigned`. However, these functions are relatively rarely
used in tactic code because we usually prefer a more powerful operation:
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
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
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
e := .fvar (FVarId.mk `h)
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
getLCtx : MetaM LocalContext
```

All operations involving fvars use this ambient local context.

The downside of this setup is that we always need to update the ambient local
context to match the goal we are currently working on. To do this, we use
`Lean.MVarId.withContext` of type

```lean
withContext (mvarId : MVarId) (c : MetaM α) : MetaM α
```

This function takes a metavariable `mvarId` and a `MetaM` computation `c` and
executes `c` with the ambient context set to the local context of `mvarId`. A
typical use case looks like this:

```lean
def someTactic (mvarId : MVarId) ... : ... :=
  mvarId.withContext do
    ...
```

The tactic receives the current goal as the metavariable `mvarId` and
immediately sets the current local context. Any operations within the `do` block
then use the local context of `mvarId`.

Once we have the local context properly set, we can manipulate fvars. Like
metavariables, fvars are identified by an `FVarId` (a unique `Name`). Basic
operations include:

- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` retrieves the declaration
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
  if ldecl.isImplementationDetail then
    continue
  -- do something with the ldecl
```

The loop iterates over every `LocalDecl` in the context. The
`isImplementationDetail` check skips local hypotheses which are 'implementation
details', meaning they are introduced by Lean or by tactics for bookkeeping
purposes. They are not shown to users and tactics are expected to ignore them.

At this point, we can build the `MetaM` part of an `assumption` tactic:
-/

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Check that `mvarId` is not already assigned.
  mvarId.checkNotAssigned `myAssumption
  -- Use the local context of `mvarId`.
  mvarId.withContext do
    -- The target is the type of `mvarId`.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        mvarId.assign ldecl.toExpr
        -- Stop and return true.
        return true
    -- If we have not found any suitable local hypothesis, return false.
    return false

/-
The `myAssumption` tactic contains three functions we have not seen before:

- `Lean.MVarId.checkNotAssigned` checks that a metavariable is not already
  assigned. The 'myAssumption' argument is the name of the current tactic. It is
  used to generate a nicer error message.
- `Lean.Meta.isDefEq` checks whether two definitions are definitionally equal.
  See the [Definitional Equality section](#definitional-equality).
- `Lean.LocalDecl.toExpr` is a helper function which constructs the `fvar`
  expression corresponding to a local hypothesis.


### Delayed Assignments

The above discussion of metavariable assignment contains a lie by omission:
there are actually two ways to assign a metavariable. We have seen the regular
way; the other way is called a *delayed assignment*.

We do not discuss delayed assignments in any detail here since they are rarely
useful for tactic writing. If you want to learn more about them, see the
comments in `MetavarContext.lean` in the Lean standard library. But they create
two complications which you should be aware of.

First, delayed assignments make `Lean.MVarId.isAssigned` and
`getExprMVarAssignment?` medium-calibre footguns. These functions only check for
regular assignments, so you may need to use `Lean.MVarId.isDelayedAssigned`
and `Lean.Meta.getDelayedMVarAssignment?` as well.

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
represented by entirely different expressions, but our users would usually
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

#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)

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
four values: `reducible`, `instances`, `default` and `all`. Any `MetaM`
computation has access to an ambient `TransparencyMode` which can be obtained
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
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

/-!
We start with `reducible` transparency, which only unfolds `reducibleDef`:
-/

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

/-!
If we repeat the above command but let Lean print implicit arguments as well,
we can see that the `+` notation amounts to an application of the `hAdd`
function, which is a member of the `HAdd` typeclass:
-/

set_option pp.explicit true
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1

/-!
When we reduce with `instances` transparency, this applications is unfolded and
replaced by `Nat.add`:
-/

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
With `default` transparency, `Nat.add` is unfolded as well:
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
additionally reduces to `Y ∨ Z`, the specific `Y` and `Z` do not concern us.
Reducing `P` would be unnecessary work.

This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

and `f` cannot be reduced (at the current transparency). To conveniently check
the WHNF of an expression, we define a function `whnf'`, using some functions
that will be discussed in the Elaboration chapter.
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

Applications of constants are not in WHNF if the current transparency allows us
to unfold the constants:
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
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
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
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
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
*unifies* `t` and `u`; such unification queries are sometimes written `t =?= u`.
For instance, the unification `List ?m =?= List Nat` succeeds and assigns `?m :=
Nat`. The unification `Nat.succ ?m =?= n + 1` succeeds and assigns `?m := n`.
The unification `?m₁ + ?m₂ + ?m₃ =?= m + n - k` fails and no metavariables are
assigned (even though there is a 'partial match' between the expressions).

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


## Constructing Expressions

In the previous chapter, we saw some primitive functions for building
expressions: `Expr.app`, `Expr.const`, `mkAppN` and so on. There is nothing
wrong with these functions, but the additional facilities of `MetaM` often
provide more convenient ways.


### Applications

When we write regular Lean code, Lean helpfully infers many implicit arguments
and universe levels. If it did not, our code would look rather ugly: -/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend
-- def appendAppend.{u_1} : {α : Type u_1} → List.{u_1} α → List.{u_1} α → List.{u_1} α :=
-- fun {α : Type u_1} (xs ys : List.{u_1} α) => @List.append.{u_1} α (@List.append.{u_1} α xs ys) xs

/-!
The `.{u_1}` suffixes are universe levels, which must be given for every
polymorphic constant. And of course the type `α` is passed around everywhere.

Exactly the same problem occurs during metaprogramming when we construct
expressions. A hand-made expression representing the right-hand side of the
above definition looks like this:
-/

def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

/-!
Having to specify the implicit arguments and universe levels is annoying and
error-prone. So `MetaM` provides a helper function which allows us to omit
implicit information: `Lean.Meta.mkAppM` of type

```lean
mkAppM : Name → Array Expr → MetaM Expr
```

Like `mkAppN`, `mkAppM` constructs an application. But while `mkAppN` requires
us to give all universe levels and implicit arguments ourselves, `mkAppM` infers
them. This means we only need to provide the explicit arguments, which makes for
a much shorter example:
-/

def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

/-!
Note the absence of any `α`s and `u`s. There is also a variant of `mkAppM`,
`mkAppM'`, which takes an `Expr` instead of a `Name` as the first argument,
allowing us to construct applications of expressions which are not constants.

However, `mkAppM` is not magic: if you write `mkAppM ``List.append #[]`, you
will get an error at runtime. This is because `mkAppM` tries to determine what
the type `α` is, but with no arguments given to `append`, `α` could be anything,
so `mkAppM` fails.

Another occasionally useful variant of `mkAppM` is `Lean.Meta.mkAppOptM` of type

```lean
mkAppOptM : Name → Array (Option Expr) → MetaM Expr
```

Whereas `mkAppM` always infers implicit and instance arguments and always
requires us to give explicit arguments, `mkAppOptM` lets us choose freely which
arguments to provide and which to infer. With this, we can, for example, give
instances explicitly, which we use in the following example to give a
non-standard `Ord` instance.
-/

def revOrd : Ord Nat where
  compare x y := compare y x

def ordExpr : MetaM Expr := do
  mkAppOptM ``compare #[none, Expr.const ``revOrd [], mkNatLit 0, mkNatLit 1]

#eval format <$> ordExpr
-- Ord.compare.{0} Nat revOrd
--   (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
--   (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))

/-!
Like `mkAppM`, `mkAppOptM` has a primed variant `Lean.Meta.mkAppOptM'` which
takes an `Expr` instead of a `Name` as the first argument. The file which
contains `mkAppM` also contains various other helper functions, e.g. for making
list literals or `sorry`s.


### Lambdas and Foralls

Another common task is to construct expressions involving `λ` or `∀` binders.
Suppose we want to create the expression `λ (x : Nat), Nat.add x x`. One way is
to write out the lambda directly:
-/

def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x

/-!
This works, but the use of `bvar` is highly unidiomatic. Lean uses a so-called
*locally closed* variable representation. This means that all but the
lowest-level functions in the Lean API expect expressions not to contain 'loose
`bvar`s', where a `bvar` is loose if it is not bound by a binder in the same
expression. (Outside of Lean, such variables are usually called 'free'. The name
`bvar` -- 'bound variable' -- already indicates that `bvar`s are never supposed
to be free.)

As a result, if in the above example we replace `mkAppN` with the slightly
higher-level `mkAppM`, we get a runtime error. Adhering to the locally closed
convention, `mkAppM` expects any expressions given to it to have no loose bound
variables, and `.bvar 0` is precisely that.

So instead of using `bvar`s directly, the Lean way is to construct expressions
with bound variables in two steps:

1. Construct the body of the expression (in our example: the body of the
   lambda), using temporary local hypotheses (`fvar`s) to stand in for the bound
   variables.
2. Replace these `fvar`s with `bvar`s and, at the same time, add the
   corresponding lambda binders.

This process ensures that we do not need to handle expressions with loose
`bvar`s at any point (except during step 2, which is performed 'atomically' by a
bespoke function). Applying the process to our example:

-/

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

/-!
There are two new functions. First, `Lean.Meta.withLocalDecl` has type

```lean
withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α
```

Given a variable name, binder info and type, `withLocalDecl` constructs a new
`fvar` and passes it to the computation `k`. The `fvar` is available in the local
context during the execution of `k` but is deleted again afterwards.

The second new function is `Lean.Meta.mkLambdaFVars` with type (ignoring some
optional arguments)

```
mkLambdaFVars : Array Expr → Expr → MetaM Expr
```

This function takes an array of `fvar`s and an expression `e`. It then adds one
lambda binder for each `fvar` `x` and replaces every occurrence of `x` in `e`
with a bound variable corresponding to the new lambda binder. The returned
expression does not contain the `fvar`s any more, which is good since they
disappear after we leave the `withLocalDecl` context. (Instead of `fvar`s, we
can also give `mvar`s to `mkLambdaFVars`, despite its name.)

Some variants of the above functions may be useful:

- `withLocalDecls` declares multiple temporary `fvar`s.
- `mkForallFVars` creates `∀` binders instead of `λ` binders. `mkLetFVars`
  creates `let` binders.
- `mkArrow` is the non-dependent version of `mkForallFVars` which construcs
  a function type `X → Y`. Since the type is non-dependent, there is no need
  for temporary `fvar`s.

Using all these functions, we can construct larger expressions such as this one:

```lean
λ (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)
```
-/

def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow (.const ``Nat []) (.const ``Nat [])
  withLocalDecl `f BinderInfo.default funcType fun f => do
    let feqn ← withLocalDecl `n BinderInfo.default (.const ``Nat []) fun n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

/-!
The next line registers `someProp` as a name for the expression we've just
constructed, allowing us to play with it more easily. The mechanisms behind this
are discussed in the Elaboration chapter.
-/

elab "someProp" : term => somePropExpr

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)


/-!
### Deconstructing Expressions

Just like we can construct expressions more easily in `MetaM`, we can also
deconstruct them more easily. Particularly useful is a family of functions for
deconstructing expressions which start with `λ` and `∀` binders.

When we are given a type of the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, we are
often interested in doing something with the conclusion `U`. For instance, the
`apply` tactic, when given an expression `e : ∀ ..., U`, compares `U` with the
current target to determine whether `e` can be applied.

To do this, we could repeatedly match on the type expression, removing `∀`
binders until we get to `U`. But this would leave us with an `U` containing
unbound `bvar`s, which, as we saw, is bad. Instead, we use
`Lean.Meta.forallTelescope` of type

```
forallTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α
```

Given `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`, this function creates one
fvar `fᵢ` for each `∀`-bound variable `xᵢ` and replaces each `xᵢ` with `fᵢ` in
the conclusion `U`. It then calls the computation `k`, passing it the `fᵢ` and
the conclusion `U f₁ ... fₙ`. Within this computation, the `fᵢ` are registered
in the local context; afterwards, they are deleted again (similar to
`withLocalDecl`).

There are many useful variants of `forallTelescope`:

- `forallTelescopeReducing`: like `forallTelescope` but matching is performed up
  to computation. This means that if you have an expression `X` which is
  different from but defeq to `∀ x, P x`, `forallTelescopeReducing X` will
  deconstruct `X` into `x` and `P x`. The non-reducing `forallTelescope` would
  not recognise `X` as a quantified expression. The matching is performed by
  essentially calling `whnf` repeatedly, using the ambient transparency.
- `forallBoundedTelescope`: like `forallTelescopeReducing` (even though there is
  no "reducing" in the name) but stops after a specified number of `∀` binders.
- `forallMetaTelescope`, `forallMetaTelescopeReducing`,
  `forallMetaBoundedTelescope`: like the corresponding non-`meta` functions, but
  the bound variables are replaced by new `mvar`s instead of `fvar`s. Unlike the
  non-`meta` functions, the `meta` functions do not delete the new metavariables
  after performing some computation, so the metavariables remain in the
  environment indefinitely.
- `lambdaTelescope`, `lambdaTelescopeReducing`, `lambdaBoundedTelescope`,
  `lambdaMetaTelescope`: like the corresponding `forall` functions, but for
  `λ` binders instead of `∀`.

Using one of the telescope functions, we can implement our own `apply` tactic:
-/

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

/-!
The real `apply` does some additional pre- and postprocessing, but the core
logic is what we show here. To test our tactic, we need an elaboration
incantation, more about which in the Elaboration chapter.
-/

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a


/-!
## Backtracking

Many tactics naturally require backtracking: the ability to go back to a
previous state, as if the tactic had never been executed. A few examples:

- `first | t | u` first executes `t`. If `t` fails, it backtracks and executes
  `u`.
- `try t` executes `t`. If `t` fails, it backtracks to the initial state,
  erasing any changes made by `t`.
- `trivial` attempts to solve the goal using a number of simple tactics
  (e.g. `rfl` or `contradiction`). After each unsuccessful application of such a
  tactic, `trivial` backtracks.

Good thing, then, that Lean's core data structures are designed to enable easy
and efficient backtracking. The corresponding API is provided by the
`Lean.MonadBacktrack` class. `MetaM`, `TermElabM` and `TacticM` are all
instances of this class. (`CoreM` is not but could be.)

`MonadBacktrack` provides two fundamental operations:

- `Lean.saveState : m s` returns a representation of the current state, where
  `m` is the monad we are in and `s` is the state type. E.g. for `MetaM`,
  `saveState` returns a `Lean.Meta.SavedState` containing the current
  environment, the current `MetavarContext` and various other pieces of
  information.
- `Lean.restoreState : s → m Unit` takes a previously saved state and restores
  it. This effectively resets the compiler state to the previous point.

With this, we can roll our own `MetaM` version of the `try` tactic:
-/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-!
We first save the state, then execute `x`. If `x` fails, we backtrack the state.

The standard library defines many combinators like `tryM`. Here are the most
useful ones:

- `Lean.withoutModifyingState (x : m α) : m α` executes the action `x`, then
  resets the state and returns `x`'s result. You can use this, for example, to
  check for definitional equality without assigning metavariables:
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  If `isDefEq` succeeds, it may assign metavariables in `x` and `y`. Using
  `withoutModifyingState`, we can make sure this does not happen.
- `Lean.observing? (x : m α) : m (Option α)` executes the action `x`. If `x`
  succeeds, `observing?` returns its result. If `x` fails (throws an exception),
  `observing?` backtracks the state and returns `none`. This is a more
  informative version of our `tryM` combinator.
- `Lean.commitIfNoEx (x : α) : m α` executes `x`. If `x` succeeds,
  `commitIfNoEx` returns its result. If `x` throws an exception, `commitIfNoEx`
  backtracks the state and rethrows the exception.

Note that the builtin `try ... catch ... finally` does not perform any
backtracking. So code which looks like this is probably wrong:

```lean
try
  doSomething
catch e =>
  doSomethingElse
```

The `catch` branch, `doSomethingElse`, is executed in a state containing
whatever modifications `doSomething` made before it failed. Since we probably
want to erase these modifications, we should write instead:

```lean
try
  commitIfNoEx doSomething
catch e =>
  doSomethingElse
```

Another `MonadBacktrack` gotcha is that `restoreState` does not backtrack the
*entire* state. Caches, trace messages and the global name generator, among
other things, are not backtracked, so changes made to these parts of the state
are not reset by `restoreState`. This is usually what we want: if a tactic
executed by `observing?` produces some trace messages, we want to see them even
if the tactic fails. See `Lean.Meta.SavedState.restore` and `Lean.Core.restore`
for details on what is and is not backtracked.

In the next chapter, we move towards the topic of elaboration, of which
you've already seen several glimpses in this chapter. We start by discussing
Lean's syntax system, which allows you to add custom syntactic constructs to the
Lean parser.

## Exercises

1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
Notice that changing the type of the metavariable from `Nat` to, for example, `String`, doesn't raise any errors - that's why, as was mentioned, we must make sure *"(a) that `val` must have the target type of `mvarId` and (b) that `val` must only contain `fvars` from the local context of `mvarId`"*.
2. [**Metavariables**] What would `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output?
3. [**Metavariables**] Fill in the missing lines in the following code.

    ```lean
    #eval show MetaM Unit from do
      let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
      let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

      -- Create `mvar1` with type `Nat`
      -- let mvar1 ← ...
      -- Create `mvar2` with type `Nat`
      -- let mvar2 ← ...
      -- Create `mvar3` with type `Nat`
      -- let mvar3 ← ...

      -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
      -- ...

      -- Assign `mvar3` to `1`
      -- ...

      -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
      ...
    ```
4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below.
  **a)** What would be the `type` and `userName` of metavariable `mvarId`?
  **b)** What would be the `type`s and `userName`s of all local declarations in this metavariable's local context?
  Print them all out.

    ```lean
    elab "explore" : tactic => do
      let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
      let metavarDecl : MetavarDecl ← mvarId.getDecl

      IO.println "Our metavariable"
      -- ...

      IO.println "All of its local declarations"
      -- ...

    theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
      explore
      sorry
    ```
5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.
6. [**Computation**] What is the normal form of the following expressions:
  **a)** `fun x => x` of type `Bool → Bool`
  **b)** `(fun x => x) ((true && false) || true)` of type `Bool`
  **c)** `800 + 2` of type `Nat`
7. [**Computation**] Show that `1` created with `Expr.lit (Lean.Literal.natVal 1)` is definitionally equal to an expression created with `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])`.
8. [**Computation**] Determine whether the following expressions are definitionally equal. If `Lean.Meta.isDefEq` succeeds, and it leads to metavariable assignment, write down the assignments.
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
  **b)** `2 + 1 =?= 1 + 2`
  **c)** `?a =?= 2`, where `?a` has a type `String`
  **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type
  **e)** `2 + ?a =?= 3`
  **f)** `2 + ?a =?= 2 + 1`
9. [**Computation**] Write down what you expect the following code to output.

    ```lean
    @[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
    @[instance] def instanceDef       : Nat := 2 -- same as `instance`
    def defaultDef                    : Nat := 3
    @[irreducible] def irreducibleDef : Nat := 4

    @[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

    #eval show MetaM Unit from do
      let constantExpr := Expr.const `sum []

      Meta.withTransparency Meta.TransparencyMode.reducible do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.instances do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.default do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      Meta.withTransparency Meta.TransparencyMode.all do
        let reducedExpr ← Meta.reduce constantExpr
        dbg_trace (← ppExpr reducedExpr) -- ...

      let reducedExpr ← Meta.reduce constantExpr
      dbg_trace (← ppExpr reducedExpr) -- ...
    ```
10. [**Constructing Expressions**] Create expression `fun x, 1 + x` in two ways:
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  In what version can you use `Lean.mkAppN`? In what version can you use `Lean.Meta.mkAppM`?
11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`.
12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways:
  **a)** not idiomatically, with loose bound variables
  **b)** idiomatically.
  In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
13. [**Constructing Expressions**] Create expression `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
14. [**Constructing Expressions**] What would you expect the output of the following code to be?

    ```lean
    #eval show Lean.Elab.Term.TermElabM _ from do
      let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
      let expr ← Elab.Term.elabTermAndSynthesize stx none

      let (_, _, conclusion) ← forallMetaTelescope expr
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
      dbg_trace conclusion -- ...

      let (_, _, conclusion) ← lambdaMetaTelescope expr
      dbg_trace conclusion -- ...
    ```
15. [**Backtracking**] Check that the expressions `?a + Int` and `"hi" + ?b` are definitionally equal with `isDefEq` (make sure to use the proper types or `Option.none` for the types of your metavariables!).
Use `saveState` and `restoreState` to revert metavariable assignments.
-/
