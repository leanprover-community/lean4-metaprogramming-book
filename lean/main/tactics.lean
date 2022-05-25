import Lean.Elab.Tactic
open Lean.Elab.Tactic
/-
# Tactics

Tactics too are Lean programs that manipulate a custom state.
All tactics are of type `TacticM Unit`. This has the type:

```lean
-- Lean/Elab/Tactic/Basic.lean
TacticM = ReaderT Context $ StateRefT State TermElabM
```
The goals of the proof state is represented by metavariables (`MVarId`).


## The simplest tactic: `sorry`

In this section, we wish to write a tactic that fills the proof with sorry:

```
theorem wrong : 1 = 2 := by {
  custom_sorry
}

#print wrong
-- theorem wrong : 1 = 2 :=
--   sorryAx (1 = 2)
```

We begin by declaring such a tactic:
-/


elab "custom_sorry_0" : tactic => do
    let goal <- Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"1) goal: {goal.name}"

theorem wrong : 1 = 2 := by {
  custom_sorry_0
  -- 1) goal: _uniq.461
  -- unsolved goals: ⊢ 1 = 2
}

/-
This defines a syntax extension to Lean, where we are naming
the piece of syntax `admit` as living `tactic` syntax category. This
informs the elaborator that in the context of elaborating `tactic`s,
the piece of syntax `admit` must be elaborated as what we
write to the right-hand-side of the `=>` (we fill the `...` with the body
of the tactic).
-/


/-
Next, we write a term in `TacticM Unit` which fills in the goal
with a `sorryAx _`. To do this, we need to first access the goal,
and then we need to fill the goal in with a `sorryAx`. We access the
goal with `Lean.Elab.Tactic.getMainGoal : Tactic MVarId`, which returns
the main goal, represented as a metavariable. Recall that under types-as-propositions,
the type of our goal must be the proposition that `1 = 2`.
We check this by printing the type of `goal`.
-/

elab "custom_sorry_1" : tactic => do
    let goal <- Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"1) goal: {goal.name}"
    let goal_declaration <- Lean.Meta.getMVarDecl goal
    let goal_type := goal_declaration.type
    dbg_trace f!"2) goal type: {goal_type}"

theorem wrong_1 : 1 = 2 := by {
  custom_sorry_1
  -- 1) goal: _uniq.757
  -- 2) goal type:
  --      Eq.{1} Nat
  --             (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
  --             (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
  -- unsolved goals: ⊢ 1 = 2
}

/-
To `sorry` the goal, we can use the helper `Lean.Elab.admitGoal`:
-/

elab "custom_sorry_2" : tactic => do
    let goal <- Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"1) goal: {goal.name}"
    let goal_declaration <- Lean.Meta.getMVarDecl goal
    let goal_type := goal_declaration.type
    dbg_trace f!"2) goal type: {goal_type}"
    Lean.Elab.admitGoal goal

theorem wrong_2 : 1 = 2 := by {
  custom_sorry_2
  -- 1) goal: _uniq.736
  -- 2) goal type:
  --      Eq.{1} Nat
  --             (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
  --             (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
}

#print wrong
-- theorem wrong : 1 = 2 :=
-- sorryAx (1 = 2)

/-
See that we no longer have the error `unsolved goals: ⊢ 1 = 2`.
-/


/-
## The `trivial` tactic: Accessing Hypotheses

In this section, we will learn how to access the hypotheses to prove
a goal. In particular, we shall attempt to implement a tactic `custom_trivial`,
which looks for an exact match of the goal amongst the hypotheses, and solves
the theorem if possible.

We expect that when we have a goal that matches a known hypothesis, the tactic
`custom_trivial` immediately solves the goal with the hypothesis. In the example
below, we expect `custom_trivial` to use `(H2: 2 = 2)` to solve the goal `(2 = 2)`:

```lean
theorem trivial_correct (H1: 1 = 1) (H2: 2 = 2): 2 = 2 := by {
  custom_trivial
}

#print trivial_correct
-- theorem trivial_correct : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2
```

When we do not have a matching hypothesis to the goal, we expect the tactic
`custom_trivial` to throw an error, telling us that we cannot find a hypothesis
of the type we are looking for:


```lean
theorem trivial_wrong (H1: 1 = 1): 2 = 2 := by {
  custom_trivial
}

#print trivial_wrong
-- tactic 'custom_trivial' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2
```


We begin by accessing the goal and the type of the goal so we know what we
are trying to prove:

-/


elab "custom_trivial_0" : tactic => do
  let goal <- Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"
  let goal_type <- Lean.Elab.Tactic.getMainTarget
  dbg_trace f!"2) goal type: {goal_type}"

theorem trivial_correct_0 (H1: 1 = 1) (H2: 2 = 2): 2 = 2 := by {
  custom_trivial_0
}

#print trivial_correct_0
-- 1) goal: _uniq.638
-- 2) goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2


theorem trivial_wrong_0 (H1: 1 = 1): 2 = 2 := by {
  custom_trivial_0
}
#print trivial_wrong_0
-- 1) goal: _uniq.713
-- 2) goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- theorem trivial_wrong : 1 = 1 → 2 = 2 :=
-- fun H1 => sorryAx (2 = 2)

/-
Next, we access the list of hypotheses, which are stored in a data structure
called `LocalContext`. This is accessed via `Lean.MonadLCtx.getLCtx`. The `LocalContext`
contains `LocalDeclaration`s, from which we can extract information such as the name that
is given to declarations (`.userName)`, the expression of the declaration `(.toExpr)`.
We write a tactic called `list_local_decls` that prints the local declarations:
-/

elab "list_local_decls_1" : tactic => do
  let lctx <- Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM (fun (ldecl: Lean.LocalDecl) => do 
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_name := ldecl.userName -- Find the name of the declaration.
      dbg_trace f!"1) local decl: name: {ldecl_name} | expr: {ldecl_expr}"
  )

theorem test_list_local_decls_1 (H1: 1 = 1) (H2: 2 = 2): 1 = 1 := by {
  list_local_decls_1
-- + local decl: nametrivial_correct_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  sorry
}



/-
Recall that we are looking for a local declaration that has the same type as the hypothesis. We
get the type of `LocalDefinition` by calling `Lean.Meta.inferType` on the local declaration's expression.
-/

elab "list_local_decls_2" : tactic => do
  let lctx <- Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM (fun (ldecl: Lean.LocalDecl) => do 
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_name := ldecl.userName -- Find the name of the declaration.
      let ldecl_type <- Lean.Meta.inferType ldecl_expr -- **NEW:** Find the type.
      dbg_trace f!"+ local decl: name: {ldecl_name} | expr: {ldecl_expr} | type: {ldecl_type}"
  )

theorem test_list_local_decls_2 (H1: 1 = 1) (H2: 2 = 2): 1 = 1 := by {
  list_local_decls_2
-- + local decl: name: test_list_local_decls_2 | expr: _uniq.4263 | type: (Eq.{1} Nat ...)
-- + local decl: name: H1 | expr: _uniq.4264 | type: Eq.{1} Nat ...)
-- + local decl: name: H2 | expr: _uniq.4265 | type: Eq.{1} Nat ...)
  sorry
}

/-
We check if the type of the `LocalDefinition` is equal to the goal type with  wih `Lean.Meta.isExprDefEq`.
See that we check if the types are equal at `eq?`, and we print that `H1` has the same type
as the goal (`local decl[EQUAL? true]: name: H1`), and we print that `H2` does not have the
same type (`local decl[EQUAL? false]: name: H2 `):
-/

elab "list_local_decls_3" : tactic => do
  let goal <- Lean.Elab.Tactic.getMainGoal
  let goal_declaration <- Lean.Meta.getMVarDecl goal
  let goal_type := goal_declaration.type
  let lctx <- Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM (fun (ldecl: Lean.LocalDecl) => do 
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_name := ldecl.userName -- Find the name of the declaration.
      let ldecl_type <- Lean.Meta.inferType ldecl_expr -- Find the type.
      let eq? <- Lean.Meta.isExprDefEq ldecl_type goal_type -- **NEW** Check if type equals goal type.
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {ldecl_name} | expr: {ldecl_expr} | type: {ldecl_type}"
  )

-- + local decl[EQUAL? false]: name: test_list_local_decls_3 | expr: _uniq.5378 | type: ...
-- + local decl[EQUAL? true]: name: H1 | expr: _uniq.5379 | type: ...
-- + local decl[EQUAL? false]: name: H2 | expr: _uniq.5380 | type: ...
theorem test_list_local_decls_3 (H1: 1 = 1) (H2: 2 = 2): 1 = 1 := by {
  list_local_decls_3
  sorry
}

/-
Finally, we put all of these parts together
to write a tactic that loops over all declarations and finds
one with the correct type. We loop over decalrations with
`lctx.findDeclM?`. We infer the type of declarations with `Lean.Meta.inferType`.
We check that the declaration has the same type as the goal with `Lean.Meta.isExprDefEq`:
-/


elab "custom_trivial_1" : tactic => do
  let goal <- Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"
  let goal_type <- Lean.Elab.Tactic.getMainTarget
  dbg_trace f!"2) goal type: {goal_type}"
  let lctx <- Lean.MonadLCtx.getLCtx

   -- Iterate over the local declarations...
   let option_matching_expr <- lctx.findDeclM? (fun (ldecl: Lean.LocalDecl) => do
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_type <- Lean.Meta.inferType ldecl_expr -- Find the type.
      dbg_trace f!"3) local decl: name={ldecl.userName} | expr: {ldecl_expr} | type: {ldecl_type}"
      if (<- Lean.Meta.isExprDefEq ldecl_type goal_type) -- Check if type equals goal type.
      then return Option.some ldecl_expr -- If equal, success!
      else return Option.none -- Not found.
  )
  dbg_trace f!"4) matching_expr: {option_matching_expr}"

theorem trivial_correct_1 (H1: 1 = 1) (H2: 2 = 2): 2 = 2 := by {
  custom_trivial_1
-- 1) goal: _uniq.1408
-- 2) goal type: ...
-- 3) local decl: name=trivial_1 | ...
-- 3) local decl: name=H1 | ...
-- 3) local decl: name=H2 | ...
-- 4) matching_expr: some _uniq.1407
sorry
}
#print trivial_correct_1
--  1 = 1 → 2 = 2 → 2 = 2 := fun H1 H2 => sorryAx (2 = 2) false

theorem trivial_wrong_1 (H1: 1 = 1): 2 = 2 := by {
  custom_trivial_1
-- 1) goal: _uniq.1488
-- 2) goal type: ...
-- 3) local decl: name=trivial_wrong | ...
-- 3) local decl: name=H1 | ...
-- 4) matching_expr: none
sorry
}
#print trivial_wrong_1
-- 1 = 1 → 2 = 2 := fun H1 => sorryAx (2 = 2) false

/-
Now that we are able to find the matching expression, we need to close the theorem by using
the match. We do this with `Lean.Elab.Tactic.closeMainGoal`. When we do not have a matching
expression, we throw an error with `Lean.Meta.throwTacticEx`, which allows us to report
an error corresponding to a given goal. When throwing this error, we format the error
using `m!"..."` which builds a `MessageData`. This provides nicer error messages than
using `f!"..."` which builds a `Format`. This is because `MessageData` also runs *delaboration*,
which allows it to convert raw Lean terms like
`(Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))`
into readable strings like`(2 = 2)`. The full code listing given below shows how
to do this:
-/


elab "custom_trivial_2" : tactic => do
  let goal <- Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"
  let goal_type <- Lean.Elab.Tactic.getMainTarget
  dbg_trace f!"2) goal type: {goal_type}"
  let lctx <- Lean.MonadLCtx.getLCtx

   let option_matching_expr <- lctx.findDeclM? (fun (ldecl: Lean.LocalDecl) => do
      let ldecl_expr := ldecl.toExpr
      let ldecl_type <- Lean.Meta.inferType ldecl_expr
      let dbg_msg <- m!"3) local decl: name={ldecl.userName} | expr: {ldecl.toExpr} | type: {ldecl_type}".toString
      dbg_trace dbg_msg
      if (<- Lean.Meta.isExprDefEq ldecl_type goal_type)
      then return Option.some ldecl_expr
      else return Option.none
  )
  match option_matching_expr with
  | .some e => Lean.Elab.Tactic.closeMainGoal e
  | none => do
    Lean.Meta.throwTacticEx `custom_trivial goal (m!"unable to find matching hypothesis of type ({goal_type})")
    return ()

theorem trivial_correct_2 (H1: 1 = 1) (H2: 2 = 2): 2 = 2 := by {
  custom_trivial_2
}
#print trivial_correct_2
-- theorem trivial_correct_2 : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2


theorem trivial_wrong_2 (H1: 1 = 1): 2 = 2 := by {
  custom_trivial_2
}
-- tactic 'custom_trivial' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2


/-
#### FAQ

In this section, we collect common patterns that are used during writing tactics,
to make it easy to find common patterns.

##### How do I use goals?
Goals are represented as metavariables. The module `Lean.Elab.Tactic.Basic` has
many functions to add new goals, switch goals, etc.

##### How do I get the main goal?
Use `Lean.Elab.Tactic.getMainGoal`.
-/

elab "faq_main_goal" : tactic => do
    let goal <- Lean.Elab.Tactic.getMainGoal
    dbg_trace f!"goal: {goal.name}"

theorem test_faq_main_goal: 1 = 1 := by {
 faq_main_goal
-- goal: _uniq.9298
 sorry
}

/-
##### How do I get the list of goals?
Use `getGoals`.
-/

elab "faq_get_goals" : tactic => do
    let goals <- Lean.Elab.Tactic.getGoals
    goals.forM $ fun goal => do 
       let goal_type <- Lean.Meta.getMVarType goal
       dbg_trace f!"goal: {goal.name} | type: {goal_type}"


theorem test_faq_get_goals (b: Bool): b = true := by {
 cases b;
 faq_get_goals
-- goal: _uniq.10067 | type: Eq.{1} Bool Bool.false Bool.true
-- goal: _uniq.10078 | type: Eq.{1} Bool Bool.true Bool.true
 sorry
 sorry
}

/-
##### How do I get the current hypotheses for a goal?

Use `Lean.MonadLCtx.getLCtx` which provides the local context, and
then iterate on the `LocalDeclaration`s of the `LocalContext` with accessors
such as `foldlM` and `forM`.
-/

elab "faq_get_hypotheses" : tactic => do
  let lctx <- Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM (fun (ldecl: Lean.LocalDecl) => do 
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_type := ldecl.type -- Find the expression of the declaration.
      let ldecl_name := ldecl.userName -- Find the name of the declaration.
      dbg_trace f!" local decl: name: {ldecl_name} | expr: {ldecl_expr} | type: {ldecl_type}"
  )
theorem test_faq_get_hypotheses (H1: 1 = 1) (H2: 2 = 2): 3 = 3 := by {
  faq_get_hypotheses
-- local decl: name: test_faq_get_hypotheses | expr: _uniq.10814 | type: ...
-- local decl: name: H1 | expr: _uniq.10815 | type: ...
-- local decl: name: H2 | expr: _uniq.10816 | type: ...
  sorry
}

/-
##### How do I perform a rewrite?
TODO: explain how to use `Lean.Elab.Tactic.Rewrite
-/

/-
##### How do I evaluate a tactic?
Use `Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` which evaluates a given tactic syntax.
One can create tactic syntax using the macro `(tactic| ...)`.

For example, one call call `try rfl` with the piece of code:

```lean
Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
```
-/

/-
##### How do I check if two expressions are equal?

Use `Lean.Meta.isExprDefEq <expr-1> <expr-2>`.
-/

#check Lean.Meta.isExprDefEq
-- Lean.Meta.isExprDefEq : Lean.Expr → Lean.Expr → Lean.MetaM Bool

/-
##### How do I throw an error from a tactic?

Use `throwTacticEx <tactic-name> <goal-mvar> <error>`.
-/

elab "faq_throw_error" : tactic => do
  let goal <- getMainGoal
  Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"


theorem test_faq_throw_error (b: Bool): b = true := by {
 cases b;
 faq_throw_error
-- case true
-- ⊢ true = true
-- ▶ 469:2-469:17: error:
-- tactic 'faq_throw_error' failed, throwing an error at the current goal
-- case false
-- ⊢ false = true
}

/-
##### What is the difference between `Lean.Elab.Tactic.*` and `Lean.Meta.Tactic.*`?

`Lean.Meta.Tactic.*` contains low level code that uses the `Meta` monad to implement
basic features such as rewriting. `Lean.Elab.Tactic.*` contains high-level code that connects the low
level development in `Lean.Meta` to the tactic infrastructure and the parsing front-end.
-/
