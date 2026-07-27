import Lean.Elab.Tactic
open Lean Elab Tactic Meta

/- ### 1. -/

elab "step_1" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let Expr.app (Expr.app (Expr.const `Iff _) a) b := goalType | throwError "Goal type is not of the form `a ↔ b`"

  -- 1. Create new `_`s with appropriate types.
  let mvarId1 ← mkFreshExprMVar (Expr.forallE `xxx a b .default) (userName := `red)
  let mvarId2 ← mkFreshExprMVar (Expr.forallE `yyy b a .default) (userName := `blue)

  -- 2. Assign the main goal to the expression `Iff.intro _ _`.
  mvarId.assign (mkAppN (Expr.const `Iff.intro []) #[a, b, mvarId1, mvarId2])

  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "step_2" : tactic => do
  let some redMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red
  ) | throwError "No mvar with username `red`"
  let some blueMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `blue
  ) | throwError "No mvar with username `blue`"

  ---- HANDLE `red` goal
  let Expr.forallE _ redFrom redTo _ := (← redMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  let handyRedMvarId ← withLocalDecl `hA BinderInfo.default redFrom (fun fvar => do
    -- 1. Create new `_`s with appropriate types.
    let mvarId1 ← mkFreshExprMVar redTo MetavarKind.syntheticOpaque `red
    -- 2. Assign the main goal to the expression `fun hA => _`.
    redMvarId.assign (← mkLambdaFVars #[fvar] mvarId1)
    -- just a handy way to return a handyRedMvarId for the next code
    return mvarId1.mvarId!
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId, blueMvarId] }

  ---- HANDLE `blue` goal
  let Expr.forallE _ blueFrom _ _ := (← blueMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `fun hB : q ∧ p => (And.intro hB.right hB.left)`.
  Lean.Meta.withLocalDecl `hB .default blueFrom (fun hB => do
    let body ← Lean.Meta.mkAppM `And.intro #[← Lean.Meta.mkAppM `And.right #[hB], ← Lean.Meta.mkAppM `And.left #[hB]]
    blueMvarId.assign (← Lean.Meta.mkLambdaFVars #[hB] body)
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId] }

elab "step_3" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget
  let mainDecl ← mvarId.getDecl

  let Expr.app (Expr.app (Expr.const `And _) q) p := goalType | throwError "Goal type is not of the form `And q p`"

  -- 1. Create new `_`s with appropriate types.
  let mvarId1 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances q (userName := `red1)
  let mvarId2 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances p (userName := `red2)

  -- 2. Assign the main goal to the expression `And.intro _ _`.
  mvarId.assign (← mkAppM `And.intro #[mvarId1, mvarId2])

  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "step_4" : tactic => do
  let some red1MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red1
  ) | throwError "No mvar with username `red1`"
  let some red2MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red2
  ) | throwError "No mvar with username `red2`"

  ---- HANDLE `red1` goal
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `hA.right`.
  let some hA := (← red1MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypothesis with name `hA` (in goal `red1`)"
  red1MvarId.withContext do
    red1MvarId.assign (← mkAppM `And.right #[hA.toExpr])
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [red2MvarId] }

  ---- HANDLE `red2` goal
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `hA.left`.
  let some hA := (← red2MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypothesis with name `hA` (in goal `red2`)"
  red2MvarId.withContext do
    red2MvarId.assign (← mkAppM `And.left #[hA.toExpr])
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [] }

theorem gradual (p q : Prop) : p ∧ q ↔ q ∧ p := by
  step_1
  guard_target =ₛ p ∧ q → q ∧ p
  step_2
  guard_hyp hA :ₛ p ∧ q
  guard_target =ₛ q ∧ p
  step_3
  guard_hyp hA :ₛ p ∧ q
  guard_target =ₛ q
  step_4

/- ### 2. -/

elab "forker_a" : tactic => do
  liftMetaTactic fun mvarId => do
    let (Expr.app (Expr.app (Expr.const `And _) p) q) ← mvarId.getType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

    let mvarIdP ← mkFreshExprMVar p (userName := `red)
    let mvarIdQ ← mkFreshExprMVar q (userName := `blue)

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    return [mvarIdP.mvarId!, mvarIdQ.mvarId!]

elab "forker_b" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := `red)
    let mvarIdQ ← mkFreshExprMVar q (userName := `blue)

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    setGoals ([mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ (← getGoals).drop 1)

elab "forker_c" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := `red)
    let mvarIdQ ← mkFreshExprMVar q (userName := `blue)

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    replaceMainGoal [mvarIdP.mvarId!, mvarIdQ.mvarId!]

example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
  intro hA hB hC
  forker_a
  guard_hyp hA :ₛ A
  guard_hyp hB :ₛ B
  guard_hyp hC :ₛ C
  guard_target =ₛ A ∧ B
  forker_a
  guard_target =ₛ A
  assumption
  guard_target =ₛ B
  assumption
  guard_target =ₛ C
  assumption

/- ### 3. -/

elab "introductor_a" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.introN 2
      return [mvarIdNew]

elab "introductor_b" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.intro1P
      return [mvarIdNew]

elab "introductor_c" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let (_, mvarIdNew) ← mvarId.intro `hello
      return [mvarIdNew]

-- So:
-- `intro`   - **intro**, specify the name manually
-- `intro1`  - **intro**, make the name inacessible
-- `intro1P` - **intro**, preserve the original name
-- `introN`  - **intro many**, specify the names manually
-- `introNP` - **intro many**, preserve the original names

example (a b c : Nat) : (ab : a = b) → (bc : b = c) → a = c := by
  introductor_a
  guard_hyp ‹a = b› :ₛ a = b
  guard_hyp ‹b = c› :ₛ b = c
  guard_target =ₛ a = c
  exact Eq.trans ‹a = b› ‹b = c›

example (a b c : Nat) : (ab : a = b) → (bc : b = c) → a = c := by
  introductor_b
  guard_hyp ab :ₛ a = b
  guard_target =ₛ (bc : b = c) → a = c
  intro bc
  exact Eq.trans ab bc

example (a b c : Nat) : (ab : a = b) → (bc : b = c) → a = c := by
  introductor_c
  guard_hyp hello :ₛ a = b
  guard_target =ₛ (bc : b = c) → a = c
  intro bc
  exact Eq.trans hello bc
