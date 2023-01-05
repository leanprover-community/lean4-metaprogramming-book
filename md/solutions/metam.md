```lean
import Lean
open Lean
```

# MetaM: Solutions

1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.

```lean
#eval show MetaM Unit from do
  let hi ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `hi)
  IO.println s!"value in hi: {← instantiateMVars hi}" -- ?_uniq.1

  hi.mvarId!.assign (Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero []))
  IO.println s!"value in hi: {← instantiateMVars hi}" -- Nat.zero
```

2. [**Metavariables**] What would `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output?

```lean
-- It would output the same expression we gave it - there were no metavariables to instantiate.
#eval show MetaM Unit from do
  let instantiatedExpr ← instantiateMVars (Expr.lam `x (Expr.const `Nat []) (Expr.bvar 0) BinderInfo.default)
  IO.println instantiatedExpr -- fun (x : Nat) => x
```

3. [**Metavariables**] Fill in the missing lines in the following code...

```lean
#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  let mvar1 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar1)
  -- Create `mvar2` with type `Nat`
  let mvar2 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar2)
  -- Create `mvar3` with type `Nat`
  let mvar3 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar3)

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign (Lean.mkAppN (Expr.const `Nat.add []) #[(Lean.mkAppN (Expr.const `Nat.add []) #[twoExpr, mvar2]), mvar3])

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign oneExpr

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  let instantiatedMvar1 ← instantiateMVars mvar1
  IO.println instantiatedMvar1 -- Nat.add (Nat.add 2 ?_uniq.2) 1
```

4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below...

```lean
elab "explore" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    IO.println "Our metavariable"
    -- [anonymous] : 2 = 2
    IO.println s!"\n{metavarDecl.userName} : {metavarDecl.type}"

    IO.println "\nAll of its local declarations"
    let localContext : LocalContext := metavarDecl.lctx
    for (localDecl : LocalDecl) in localContext do
      if localDecl.isImplementationDetail then
        -- (implementation detail) red : 1 = 1 → 2 = 2 → 2 = 2
        IO.println s!"\n(implementation detail) {localDecl.userName} : {localDecl.type}"
      else
        -- hA : 1 = 1
        -- hB : 2 = 2
        IO.println s!"\n{localDecl.userName} : {localDecl.type}"

theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry
```

5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.

```lean
-- The type of our metavariable `2 + 2`. We want to find a `localDecl` that has the same type, and `assign` our metavariable to that `localDecl`.
elab "solve" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    let localContext : LocalContext := metavarDecl.lctx
    for (localDecl : LocalDecl) in localContext do
      if ← Lean.Meta.isDefEq localDecl.type metavarDecl.type then
        mvarId.assign localDecl.toExpr

theorem redSolved (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve
```
