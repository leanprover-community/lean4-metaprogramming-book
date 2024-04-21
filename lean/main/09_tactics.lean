/-
# Tactics

Tactics are Lean programs that manipulate a custom state. All tactics are, in
the end, of type `TacticM Unit`. This has the type:

```lean
-- from Lean/Elab/Tactic/Basic.lean
TacticM = ReaderT Context $ StateRefT State TermElabM
```

But before demonstrating how to use `TacticM`, we shall explore macro-based
tactics.

## Tactics by Macro Expansion

Just like many other parts of the Lean 4 infrastructure, tactics too can be
declared by lightweight macro expansion.

For example, we build an example of a `custom_sorry_macro` that elaborates into
a `sorry`. We write this as a macro expansion, which expands the piece of syntax
`custom_sorry_macro` into the piece of syntax `sorry`:
-/

import Lean.Elab.Tactic

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

example : 1 = 42 := by
  custom_sorry_macro

/-
### Implementing `trivial`: Extensible Tactics by Macro Expansion

As more complex examples, we can write a tactic such as `custom_tactic`, which
is initially completely unimplemented, and can be extended with more tactics.
We start by simply declaring the tactic with no implementation:
-/

syntax "custom_tactic" : tactic

/-- error: tactic 'tacticCustom_tactic' has not been implemented -/
#guard_msgs in --#
example : 42 = 42 := by
  custom_tactic
  sorry

/-
We will now add the `rfl` tactic into `custom_tactic`, which will allow us to
prove the previous theorem
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 42 = 42 := by
   custom_tactic
-- Goals accomplished 🎉

/-
We can now try a harder problem, that cannot be immediately dispatched by `rfl`:
-/

#check_failure (by custom_tactic : 42 = 43 ∧ 42 = 42)
-- type mismatch
--   Iff.rfl
-- has type
--   ?m.1437 ↔ ?m.1437 : Prop
-- but is expected to have type
--   42 = 43 ∧ 42 = 42 : Prop

/-
We extend the `custom_tactic` tactic with a tactic that tries to break `And`
down with `apply And.intro`, and then (recursively (!)) applies `custom_tactic`
to the two cases with `(<;> trivial)` to solve the generated subcases `43 = 43`,
`42 = 42`.
-/

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

/-
The above declaration uses `<;>` which is a *tactic combinator*. Here, `a <;> b`
means "run tactic `a`, and apply "b" to each goal produced by `a`". Thus,
`And.intro <;> custom_tactic` means "run `And.intro`, and then run
`custom_tactic` on each goal". We test it out on our previous theorem and see
that we dispatch the theorem.
-/

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic
-- Goals accomplished 🎉

/-
In summary, we declared an extensible tactic called `custom_tactic`. It
initially had no elaboration at all. We added the `rfl` as an elaboration of
`custom_tactic`, which allowed it to solve the goal `42 = 42`. We then tried a
harder theorem, `43 = 43 ∧ 42 = 42` which `custom_tactic` was unable to solve.
We were then able to enrich `custom_tactic` to split "and" with `And.intro`, and
also *recursively* call `custom_tactic` in the two subcases.

### Implementing `<;>`: Tactic Combinators by Macro Expansion

Recall that in the previous section, we said that `a <;> b` meant "run `a`, and
then run `b` for all goals". In fact, `<;>` itself is a tactic macro. In this
section, we will implement the syntax `a and_then b` which will stand for
"run `a`, and then run `b` for all goals".
-/

-- 1. We declare the syntax `and_then`
syntax tactic " and_then " tactic : tactic

-- 2. We write the expander that expands the tactic
--    into running `a`, and then running `b` on all goals produced by `a`.
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

-- 3. We test this tactic.
theorem test_and_then: 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
-- theorem test_and_then : 1 = 1 ∧ 2 = 2 :=
-- { left := Eq.refl 1, right := Eq.refl 2 }

/-
## Exploring `TacticM`

### The simplest tactic: `sorry`

In this section, we wish to write a tactic that fills the proof with sorry:

```lean
example : 1 = 2 := by
  custom_sorry
```

We begin by declaring such a tactic:
-/

elab "custom_sorry_0" : tactic => do
  return

example : 1 = 2 := by
  custom_sorry_0
-- unsolved goals: ⊢ 1 = 2
  sorry

/-
This defines a syntax extension to Lean, where we are naming the piece of syntax
`custom_sorry_0` as living in `tactic` syntax category. This informs the
elaborator that, in the context of elaborating `tactic`s, the piece of syntax
`custom_sorry_0` must be elaborated as what we write to the right-hand-side of
the `=>` (the actual implementation of the tactic).

Next, we write a term in `TacticM Unit` to fill in the goal with `sorryAx α`,
which can synthesize an artificial term of type `α`. To do this, we first access
the goal with `Lean.Elab.Tactic.getMainGoal : Tactic MVarId`, which returns the
main goal, represented as a metavariable. Recall that under
types-as-propositions, the type of our goal must be the proposition that `1 = 2`.
We check this by printing the type of `goal`.

But first we need to start our tactic with `Lean.Elab.Tactic.withMainContext`,
which computes in `TacticM` with an updated context.
-/

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

example : 1 = 2 := by
  custom_sorry_1
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals: ⊢ 1 = 2
  sorry

/-
To `sorry` the goal, we can use the helper `Lean.Elab.admitGoal`:
-/

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry
-- theorem test_custom_sorry : 1 = 2 :=
-- sorryAx (1 = 2) true

/-
And we no longer have the error `unsolved goals: ⊢ 1 = 2`.

### The `custom_assump` tactic: Accessing Hypotheses

In this section, we will learn how to access the hypotheses to prove a goal. In
particular, we shall attempt to implement a tactic `custom_assump`, which looks
for an exact match of the goal among the hypotheses, and solves the theorem if
possible.

In the example below, we expect `custom_assump` to use `(H2 : 2 = 2)` to solve
the goal `(2 = 2)`:

```lean
theorem assump_correct (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump

#print assump_correct
-- theorem assump_correct : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2
```

When we do not have a matching hypothesis to the goal, we expect the tactic
`custom_assump` to throw an error, telling us that we cannot find a hypothesis
of the type we are looking for:

```lean
theorem assump_wrong (H1 : 1 = 1) : 2 = 2 := by
  custom_assump

#print assump_wrong
-- tactic 'custom_assump' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2
```

We begin by accessing the goal and the type of the goal so we know what we
are trying to prove. The `goal` variable will soon be used to help us create
error messages.
-/

elab "custom_assump_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2
  sorry

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- ⊢ 2 = 2
  sorry

/-
Next, we access the list of hypotheses, which are stored in a data structure
called `LocalContext`. This is accessed via `Lean.MonadLCtx.getLCtx`. The
`LocalContext` contains `LocalDeclaration`s, from which we can extract
information such as the name that is given to declarations (`.userName`), the
expression of the declaration (`.toExpr`). Let's write a tactic called
`list_local_decls` that prints the local declarations:
-/

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_1
-- + local decl: name: test_list_local_decls_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  rfl

/-
Recall that we are looking for a local declaration that has the same type as the
hypothesis. We get the type of `LocalDecl` by calling
`Lean.Meta.inferType` on the local declaration's expression.
-/

elab "list_local_decls_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_2
  -- + local decl: name: test_list_local_decls_2 | expr: _uniq.4263 | type: (Eq.{1} Nat ...)
  -- + local decl: name: H1 | expr: _uniq.4264 | type: Eq.{1} Nat ...)
  -- + local decl: name: H2 | expr: _uniq.4265 | type: Eq.{1} Nat ...)
  rfl

/-
We check if the type of the `LocalDecl` is equal to the goal type with
`Lean.Meta.isExprDefEq`. See that we check if the types are equal at `eq?`, and
we print that `H1` has the same type as the goal
(`local decl[EQUAL? true]: name: H1`), and we print that `H2` does not have the
same type (`local decl[EQUAL? false]: name: H2 `):
-/

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **NEW** Check if type equals goal type.
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  rfl

/-
Finally, we put all of these parts together to write a tactic that loops over
all declarations and finds one with the correct type. We loop over declarations
with `lctx.findDeclM?`. We infer the type of declarations with
`Lean.Meta.inferType`. We check that the declaration has the same type as the
goal with `Lean.Meta.isExprDefEq`:
-/

elab "custom_assump_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.MonadLCtx.getLCtx
    -- Iterate over the local declarations...
    let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
      let declExpr := ldecl.toExpr -- Find the expression of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      if (← Lean.Meta.isExprDefEq declType goalType) -- Check if type equals goal type.
      then return some declExpr -- If equal, success!
      else return none          -- Not found.
    dbg_trace f!"matching_expr: {option_matching_expr}"

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_1
-- matching_expr: some _uniq.6241
  rfl

example (H1 : 1 = 1) : 2 = 2 := by
  custom_assump_1
-- matching_expr: none
  rfl

/-
Now that we are able to find the matching expression, we need to close the
theorem by using the match. We do this with `Lean.Elab.Tactic.closeMainGoal`.
When we do not have a matching expression, we throw an error with
`Lean.Meta.throwTacticEx`, which allows us to report an error corresponding to a
given goal. When throwing this error, we format the error using `m!"..."` which
builds a `MessageData`. This provides nicer error messages than using `f!"..."`
which builds a `Format`. This is because `MessageData` also runs *delaboration*,
which allows it to convert raw Lean terms like
`(Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))`
into readable strings like`(2 = 2)`. The full code listing given below shows how
to do this:
-/

elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
        then return Option.some declExpr
        else return Option.none
    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none =>
      Lean.Meta.throwTacticEx `custom_assump_2 goal
        (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_2

#check_failure (by custom_assump_2 : (H1 : 1 = 1) → 2 = 2)
-- tactic 'custom_assump_2' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2

/-
### Tweaking the context

Until now, we've only performed read-like operations with the context. But what
if we want to change it? In this section we will see how to change the order of
goals and how to add content to it (new hypotheses).

Then, after elaborating our terms, we will need to use the helper function
`Lean.Elab.Tactic.liftMetaTactic`, which allows us to run computations in
`MetaM` while also giving us the goal `MVarId` for us to play with. In the end
of our computation, `liftMetaTactic` expects us to return a `List MVarId` as the
resulting list of goals.

The only substantial difference between `custom_let` and `custom_have` is that
the former uses `Lean.MVarId.define` and the later uses `Lean.MVarId.assert`:
-/

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  trivial

/-
### "Getting" and "Setting" the list of goals

To illustrate these, let's build a tactic that can reverse the list of goals.
We can use `Lean.Elab.Tactic.getGoals` and `Lean.Elab.Tactic.setGoals`:
-/

elab "reverse_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals goals.reverse

theorem test_reverse_goals : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
-- case left.left
-- ⊢ 1 = 2
-- case left.right
-- ⊢ 3 = 4
-- case right
-- ⊢ 5 = 6
  reverse_goals
-- case right
-- ⊢ 5 = 6
-- case left.right
-- ⊢ 3 = 4
-- case left.left
-- ⊢ 1 = 2
  all_goals sorry

/-
## FAQ

In this section, we collect common patterns that are used during writing tactics,
to make it easy to find common patterns.

**Q: How do I use goals?**

A: Goals are represented as metavariables. The module `Lean.Elab.Tactic.Basic`
has many functions to add new goals, switch goals, etc.

**Q: How do I get the main goal?**

A: Use `Lean.Elab.Tactic.getMainGoal`.
-/

elab "faq_main_goal" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"goal: {goal.name}"

example : 1 = 1 := by
  faq_main_goal
-- goal: _uniq.9298
  rfl

/-
**Q: How do I get the list of goals?**

A: Use `getGoals`.
-/

elab "faq_get_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals ← Lean.Elab.Tactic.getGoals
    goals.forM $ fun goal => do
      let goalType ← goal.getType
      dbg_trace f!"goal: {goal.name} | type: {goalType}"

example (b : Bool) : b = true := by
  cases b
  faq_get_goals
-- goal: _uniq.10067 | type: Eq.{1} Bool Bool.false Bool.true
-- goal: _uniq.10078 | type: Eq.{1} Bool Bool.true Bool.true
  sorry
  rfl

/-
**Q: How do I get the current hypotheses for a goal?**

A: Use `Lean.MonadLCtx.getLCtx` which provides the local context, and then
iterate on the `LocalDeclaration`s of the `LocalContext` with accessors such as
`foldlM` and `forM`.
-/

elab "faq_get_hypotheses" : tactic =>
  Lean.Elab.Tactic.withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  ctx.forM (fun (decl : Lean.LocalDecl) => do
    let declExpr := decl.toExpr -- Find the expression of the declaration.
    let declType := decl.type -- Find the type of the declaration.
    let declName := decl.userName -- Find the name of the declaration.
    dbg_trace f!" local decl: name: {declName} | expr: {declExpr} | type: {declType}"
  )

example (H1 : 1 = 1) (H2 : 2 = 2): 3 = 3 := by
  faq_get_hypotheses
  -- local decl: name: _example | expr: _uniq.10814 | type: ...
  -- local decl: name: H1 | expr: _uniq.10815 | type: ...
  -- local decl: name: H2 | expr: _uniq.10816 | type: ...
  rfl

/-
**Q: How do I evaluate a tactic?**

A: Use `Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` which evaluates a
given tactic syntax. One can create tactic syntax using the macro
`` `(tactic| ⋯)``.

For example, one could call `try rfl` with the piece of code:

```lean
Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
```

**Q: How do I check if two expressions are equal?**

A: Use `Lean.Meta.isExprDefEq <expr-1> <expr-2>`.
-/

#check Lean.Meta.isExprDefEq
-- Lean.Meta.isExprDefEq : Lean.Expr → Lean.Expr → Lean.MetaM Bool

/-
**Q: How do I throw an error from a tactic?**

A: Use `throwTacticEx <tactic-name> <goal-mvar> <error>`.
-/

elab "faq_throw_error" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"

#check_failure (by faq_throw_error : (b : Bool) → b = true)
-- tactic 'faq_throw_error' failed, throwing an error at the current goal
-- ⊢ ∀ (b : Bool), b = true

/-!
**Q: What is the difference between `Lean.Elab.Tactic.*` and `Lean.Meta.Tactic.*`?**

A: `Lean.Meta.Tactic.*` contains low level code that uses the `Meta` monad to
implement basic features such as rewriting. `Lean.Elab.Tactic.*` contains
high-level code that connects the low level development in `Lean.Meta` to the
tactic infrastructure and the parsing front-end.

## Exercises

1. Consider the theorem `p ∧ q ↔ q ∧ p`. We could either write its proof as a proof term, or construct it using the tactics.
    When we are writing the proof of this theorem *as a proof term*, we're gradually filling up `_`s with certain expressions, step by step. Each such step corresponds to a tactic.

    There are many combinations of steps in which we could write this proof term - but consider the sequence of steps we wrote below. Please write each step as a tactic.
    The tactic `step_1` is filled in, please do the same for the remaining tactics (for the sake of the exercise, try to use lower-level apis, such as `mkFreshExprMVar`, `mvarId.assign` and `modify fun _ => { goals := ~)`.

    ```lean
    -- [this is the initial goal]
    example : p ∧ q ↔ q ∧ p :=
      _

    -- step_1
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro _ _

    -- step_2
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          _
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )

    -- step_3
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          (And.intro _ _)
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )

    -- step_4
    example : p ∧ q ↔ q ∧ p :=
      Iff.intro
        (
          fun hA =>
          (And.intro hA.right hA.left)
        )
        (
          fun hB =>
          (And.intro hB.right hB.left)
        )
    ```

    ```lean
    elab "step_1" : tactic => do
      let mvarId ← getMainGoal
      let goalType ← getMainTarget

      let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

      -- 1. Create new `_`s with appropriate types.
      let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := "red")
      let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := "blue")

      -- 2. Assign the main goal to the expression `Iff.intro _ _`.
      mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

      -- 3. Report the new `_`s to Lean as the new goals.
      modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }
    ```

    ```lean
    theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
      step_1
      step_2
      step_3
      step_4
    ```

2. In the first exercise, we used lower-level `modify` api to update our goals.
    `liftMetaTactic`, `setGoals`, `appendGoals`, `replaceMainGoal`, `closeMainGoal`, etc. are all syntax sugars on top of `modify fun s : State => { s with goals := myMvarIds }`.
    Please rewrite the `forker` tactic with:

    **a)** `liftMetaTactic`
    **b)** `setGoals`
    **c)** `replaceMainGoal`

    ```lean
    elab "forker" : tactic => do
      let mvarId ← getMainGoal
      let goalType ← getMainTarget

      let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId (m!"Goal is not of the form P ∧ Q")

      mvarId.withContext do
        let mvarIdP ← mkFreshExprMVar p (userName := "red")
        let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

        let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
        mvarId.assign proofTerm

        modify fun state => { goals := [mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ state.goals.drop 1 }
    ```

    ```lean
    example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
      intro hA hB hC
      forker
      forker
      assumption
      assumption
      assumption
    ```

3. In the first exercise, you created your own `intro` in `step_2` (with a hardcoded hypothesis name, but the basics are the same). When writing tactics, we usually want to use functions such as `intro`, `intro1`, `intro1P`, `introN` or `introNP`.

    For each of the points below, create a tactic `introductor` (one per each point), that turns the goal `(ab: a = b) → (bc: b = c) → (a = c)`:

    **a)** into the goal `(a = c)` with hypotheses `(ab✝: a = b)` and `(bc✝: b = c)`.
    **b)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(ab: a = b)`.
    **c)** into the goal `(bc: b = c) → (a = c)` with hypothesis `(hello: a = b)`.

    ```lean
    example (a b c : Nat) : (ab: a = b) → (bc: b = c) → (a = c) := by
      introductor
      sorry
    ```

    Hint: **"P"** in `intro1P` and `introNP` stands for **"Preserve"**.
-/
