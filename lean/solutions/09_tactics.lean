import Lean.Elab.Tactic
open Lean Elab Tactic Meta

/- ### 1. -/

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
  let mvarId1 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances q (userName := "red1")
  let mvarId2 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances p (userName := "red2")

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
  step_2
  step_3
  step_4

/- ### 2. -/

elab "forker_a" : tactic => do
  liftMetaTactic fun mvarId => do
    let (Expr.app (Expr.app (Expr.const `And _) p) q) ← mvarId.getType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    return [mvarIdP.mvarId!, mvarIdQ.mvarId!]

elab "forker_b" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    setGoals ([mvarIdP.mvarId!, mvarIdQ.mvarId!] ++ (← getGoals).drop 1)

elab "forker_c" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let (Expr.app (Expr.app (Expr.const `And _) p) q) := goalType | Lean.Meta.throwTacticEx `forker mvarId ("Goal is not of the form P ∧ Q")

  mvarId.withContext do
    let mvarIdP ← mkFreshExprMVar p (userName := "red")
    let mvarIdQ ← mkFreshExprMVar q (userName := "blue")

    let proofTerm := mkAppN (Expr.const `And.intro []) #[p, q, mvarIdP, mvarIdQ]
    mvarId.assign proofTerm

    replaceMainGoal [mvarIdP.mvarId!, mvarIdQ.mvarId!]

example (A B C : Prop) : A → B → C → (A ∧ B) ∧ C := by
  intro hA hB hC
  forker_a
  forker_a
  assumption
  assumption
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
      let (_, mvarIdNew) ← mvarId.intro `wow
      return [mvarIdNew]

-- So:
-- `intro`   - **intro**, specify the name manually
-- `intro1`  - **intro**, make the name inacessible
-- `intro1P` - **intro**, preserve the original name
-- `introN`  - **intro many**, specify the names manually
-- `introNP` - **intro many**, preserve the original names

example (a b c : Nat) : (ab: a = b) → (bc: b = c) → (a = c) := by
  introductor_a
  -- introductor_b
  -- introductor_c
  sorry

/- ### 4. -/

elab "incredibly_helpful" : tactic => do
  withMainContext do
    liftMetaTactic fun mvarId => do
      let mvarId1 ← mvarId.assert `yellow (Expr.const `String []) (mkStrLit "hi")
      let mvarId2 ← mvarId1.assert `TRUTH (Expr.const `True []) (Expr.const `True.intro [])
      let mvarId3 ← mvarId2.assert `orange (Expr.const `Nat []) (mkNatLit 8)
      return [mvarId3]

example (n : Int) : ∃ m, n + n = m := by
  incredibly_helpful
  intros
  apply Exists.intro (n + n)
  rfl

/- ### 5. -/

elab "andify " a:ident b:ident : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let lctx ← getLCtx

    let some declA := lctx.findFromUserName? a.getId | throwTacticEx `andify goal "Hypothesis a wasn't found"
    let some declB := lctx.findFromUserName? b.getId | throwTacticEx `andify goal "Hypothesis b wasn't found"

    liftMetaTactic fun mvarId => do
      -- => And a b
      let type := Expr.app (Expr.app (Expr.const `And []) declA.type) declB.type
      -- => And.intro hA hB
      let expr := Expr.app (Expr.app (Expr.const `And.intro []) declA.toExpr) declB.toExpr
      let mvarIdNew ← mvarId.assert `HELLO type expr
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

example (a b c : Nat) (ab: a = b) (bc: b = c) : (a = c) := by
  andify ab bc
  rw [ab]
  rw [bc]
