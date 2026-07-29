import Lean
open Lean Meta

/- ## `MetaM`: Solutions -/

/- ### 1. -/

/--
info: value in hi: ?hi
value in hi: 3
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let hi ← mkFreshExprMVar (Expr.const `Nat []) (userName := `hi)
  let value ← instantiateMVars hi
  IO.println s!"value in hi: {← ppExpr value}"

  hi.mvarId!.assign (Expr.lit (.natVal 3))
  let valueAssigned ← instantiateMVars hi
  IO.println s!"value in hi: {← ppExpr valueAssigned}"

/- ### 2. -/

-- It would output the same expression we gave it
-- because there were no metavariables to instantiate.
/--
info:
before: Nat.add 1 2
after: Nat.add 1 2
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let expr := Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]
  IO.println s!"before: {← ppExpr expr}"

  let instantiatedExpr ← instantiateMVars expr
  IO.println s!"after: {← ppExpr instantiatedExpr}"

/- ### 3. -/

open Lean Meta in

set_option pp.fieldNotation false in

/-- info: Nat.add (Nat.add 2 ?mvar2) 1 -/
#guard_msgs in --#
#eval show MetaM Unit from do
  let «1» := Lean.mkNatLit 1
  let «2» := Lean.mkNatLit 2
  let «Nat» := Expr.const `Nat []
  let «Nat.add» := Expr.const `Nat.add []

  -- Create `mvar1` with type `Nat`
  let mvar1 ← mkFreshExprMVar «Nat» (userName := `mvar1)
  -- Create `mvar2` with type `Nat`
  let mvar2 ← mkFreshExprMVar «Nat» (userName := `mvar2)
  -- Create `mvar3` with type `Nat`
  let mvar3 ← mkFreshExprMVar «Nat» (userName := `mvar3)

  -- Assign `mvar1` to `Nat.add (Nat.add 2 ?mvar2) ?mvar3`
  mvar1.mvarId!.assign <|
    let «Nat.add 2 ?mvar2» := Lean.mkApp2 (f := «Nat.add») «2» mvar2
    Lean.mkApp2 (f := «Nat.add») «Nat.add 2 ?mvar2» mvar3

  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign «1»

  -- Instantiate `mvar1`, which should result in expression `Nat.add (Nat.add 2 ?mvar2) 1`
  let instantiatedMvar1 ← instantiateMVars mvar1
  IO.println <| ← ppExpr instantiatedMvar1

/- ### 4. -/

elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println s!"{metavarDecl.userName} : {← ppExpr metavarDecl.type}"

  IO.println "All of its local declarations"
  let localContext : LocalContext := metavarDecl.lctx
  for (localDecl : LocalDecl) in localContext do
    if localDecl.isImplementationDetail then
      IO.println s!"(implementation detail) {localDecl.userName} : {← ppExpr localDecl.type}"
    else
      IO.println s!"{localDecl.userName} : {← ppExpr localDecl.type}"

/--
info: Our metavariable
[anonymous] : 2 = 2
All of its local declarations
(implementation detail) red : 1 = 1 → 2 = 2 → 2 = 2
hA : 1 = 1
hB : 2 = 2
-/
#guard_msgs in --#
theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  cases hA
  exact hB

/- ### 5. -/

-- The type of our metavariable `2 + 2`.
-- We want to find a `localDecl` that has the same type, and `assign` our metavariable to that `localDecl`.
elab "solve" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  let localContext : LocalContext := metavarDecl.lctx
  for (localDecl : LocalDecl) in localContext do
    if ← Lean.Meta.isDefEq localDecl.type metavarDecl.type then
      mvarId.assign localDecl.toExpr

theorem redSolved (_hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve

/- ### 6. -/

def sixA : Bool → Bool := fun x => x

/-- info: Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) (Lean.BinderInfo.default) -/
#guard_msgs in --#
#eval Lean.Meta.reduce (Expr.const `sixA [])

def sixB : Bool := (fun x => x) ((true && false) || true)

/-- info: Lean.Expr.const `Bool.true [] -/
#guard_msgs in --#
#eval Lean.Meta.reduce (Expr.const `sixB [])

def sixC : Nat := 800 + 2

/-- info: Lean.Expr.lit (Lean.Literal.natVal 802) -/
#guard_msgs in --#
#eval Lean.Meta.reduce (Expr.const `sixC [])

/- ### 7. -/

#eval show MetaM Unit from do
  let «1» := Expr.lit (Lean.Literal.natVal 1)
  let «Nat.succ Nat.zero» := Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])

  let isEqual ← Lean.Meta.isDefEq «1» «Nat.succ Nat.zero»
  assert! isEqual

/- ### 8. -/

namespace Ex8.a
  -- a) `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
  -- Definitionally equal.

  def rhs := (fun _x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))

  /-- info: true -/
  #guard_msgs in --#
  #eval show MetaM Unit from do
    let «5» := Lean.mkNatLit 5
    let «rhs» : Expr := Expr.const ``Ex8.a.rhs []
    let isEqual ← Lean.Meta.isDefEq «5» «rhs»
    IO.println isEqual

end Ex8.a

-- b) `Nat.add 2 1 =?= Nat.add 1 2`
-- Definitionally equal.
/-- info: true -/
#guard_msgs in --#
#eval show MetaM Unit from do
  let «Nat.add 2 1» := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  let «Nat.add 1 2» := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Lean.mkNatLit 2]
  let isEqual ← Lean.Meta.isDefEq «Nat.add 2 1» «Nat.add 1 2»
  IO.println isEqual

-- c) `?a =?= 2`, where `?a` has a type `String`
-- Not definitionally equal.
/-- info: false -/
#guard_msgs in --#
#eval show MetaM Unit from do
  let «?a» ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `a)
  let «2» := Lean.mkNatLit 2
  let isEqual ← Lean.Meta.isDefEq «?a» «2»
  IO.println isEqual

-- d) `Nat.add ?a Int =?= Nat.add "hi" ?b`, where `?a` and `?b` don't have a type
-- Definitionally equal.
-- `?a` is assigned to `"hi"`, `?b` is assigned to `Int`.
/--
info: true
a: "hi"
b: Int
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (type? := none) (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar (type? := none) (userName := `b)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  let expr2 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"

-- e) `Nat.add 2 ?a =?= 3`
-- Not definitionally equal.
/-- info: false -/
#guard_msgs in --#
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let expr2 := Lean.mkNatLit 3
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

-- f) `Nat.add 2 ?a =?= Nat.add 2 1`
-- Definitionally equal.
-- `?a` is assigned to `1`.
/--
info: true
a: 1
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `a)
  let expr1 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, a]
  let expr2 := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 2, Lean.mkNatLit 1]
  let isEqual ← Lean.Meta.isDefEq expr1 expr2
  IO.println isEqual

  let aValue ← instantiateMVars a
  IO.println s!"a: {← ppExpr aValue}"

/- ### 9. -/
@[reducible] def reducibleDef : Nat := 1 -- same as `abbrev`
@[instance_reducible] def instanceDef : Nat := 2
def defaultDef : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

/--
info: [1, instanceDef, defaultDef, irreducibleDef]
[1, 2, defaultDef, irreducibleDef]
[1, 2, 3, irreducibleDef]
[1, 2, 3, 4]
[1, 2, 3, irreducibleDef]
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr)

  -- Note: if we don't set the transparency mode, we get a pretty strong `TransparencyMode.default`.
  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr)

/- ### 10. -/

-- Non-idiomatic: we can only use `Lean.mkAppN`.
def tenA : MetaM Expr := do
  let body := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0]
  return Expr.lam `x (Expr.const `Nat []) body BinderInfo.default

-- Idiomatic: we can use both `Lean.mkAppN` and `Lean.Meta.mkAppM`.
def tenB : MetaM Expr := do
  Lean.Meta.withLocalDecl `x .default (Expr.const `Nat []) (fun x => do
    -- let body := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, x]
    let body ← Lean.Meta.mkAppM `Nat.add #[Lean.mkNatLit 1, x]
    Lean.Meta.mkLambdaFVars #[x] body
  )

/-- info: fun x => Nat.add 1 x -/
#guard_msgs in --#
#eval show MetaM _ from do
  ppExpr (← tenA)

/-- info: fun x => Nat.add 1 x -/
#guard_msgs in --#
#eval show MetaM _ from do
  ppExpr (← tenB)

/- ### 11. -/

def eleven : MetaM Expr :=
  return Expr.forallE `yellow (Expr.sort Level.zero) (Expr.bvar 0) BinderInfo.default

/-- info: ∀ (yellow : Prop), yellow -/
#guard_msgs in --#
#eval show MetaM _ from do
  let expr ← eleven
  dbg_trace (← ppExpr expr)

/- ### 12. -/

-- Non-idiomatic: we can only use `Lean.mkApp3`.
def twelveA : MetaM Expr := do
  let nPlusOne := Expr.app (Expr.app (Expr.const `Nat.add []) (Expr.bvar 0)) (Lean.mkNatLit 1)
  let forAllBody := Lean.mkApp3 (Expr.const ``Eq [1]) (Expr.const `Nat []) (Expr.bvar 0) nPlusOne
  let forAll := Expr.forallE `n (Expr.const `Nat []) forAllBody BinderInfo.default
  return forAll

-- Idiomatic: we can use both `Lean.mkApp3` and `Lean.Meta.mkEq`.
def twelveB : MetaM Expr := do
  withLocalDecl `n BinderInfo.default (Expr.const `Nat []) (fun x => do
    let nPlusOne := Expr.app (Expr.app (Expr.const `Nat.add []) x) (Lean.mkNatLit 1)
    -- let forAllBody := Lean.mkApp3 (Expr.const ``Eq []) (Expr.const `Nat []) x nPlusOne
    let forAllBody ← Lean.Meta.mkEq x nPlusOne
    let forAll := mkForallFVars #[x] forAllBody
    forAll
  )

section

  set_option pp.fieldNotation false

  /-- info: ∀ (n : Nat), n = Nat.add n 1 -/
  #guard_msgs in --#
  #eval show MetaM _ from do
    ppExpr (← twelveA)

  /-- info: ∀ (n : Nat), n = Nat.add n 1 -/
  #guard_msgs in --#
  #eval show MetaM _ from do
    ppExpr (← twelveB)

end
/- ### 13. -/
def thirteen : MetaM Expr := do
  withLocalDecl `f BinderInfo.default (Expr.forallE `a (Expr.const `Nat []) (Expr.const `Nat []) .default) (fun y => do
    let lamBody ← withLocalDecl `n BinderInfo.default (Expr.const `Nat []) (fun x => do
      let fn := Expr.app y x
      let fnPlusOne := Expr.app y (Expr.app (Expr.app (Expr.const `Nat.add []) (x)) (Lean.mkNatLit 1))
      let forAllBody := mkApp3 (mkConst ``Eq []) (Expr.const `Nat []) fn fnPlusOne
      let forAll := mkForallFVars #[x] forAllBody
      forAll
    )
    let lam := mkLambdaFVars #[y] lamBody
    lam
  )

/-- info: fun f => (n : Nat) → Eq Nat (f n) (f (n.add 1)) -/
#guard_msgs in --#
#eval show MetaM _ from do
  ppExpr (← thirteen)

/- ### 14. -/

/--
info: ?a✝ ∧ ?a✝
?a✝ ∨ ?b✝ → ?b✝ → ?a✝ ∧ ?a✝
∀ (a b : Prop), a ∨ b → b → a ∧ a
-/
#guard_msgs in --#
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace (← ppExpr conclusion)

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace (← ppExpr conclusion)

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace (← ppExpr conclusion)

/- ### 15. -/

/--
info: value in c: Nat.add ?a Int
value in d: Nat.add "hi" ?b

Saved state

true
value in c: Nat.add "hi" Int
value in d: Nat.add "hi" Int

Restored state

value in c: Nat.add ?a Int
value in d: Nat.add "hi" ?b
-/
#guard_msgs in --#
#eval show MetaM Unit from do
  let a ← Lean.Meta.mkFreshExprMVar (Expr.const `String []) (userName := `a)
  let b ← Lean.Meta.mkFreshExprMVar (Expr.sort (Nat.toLevel 1)) (userName := `b)
  -- ?a + Int
  let c := Lean.mkAppN (Expr.const `Nat.add []) #[a, Expr.const `Int []]
  -- "hi" + ?b
  let d := Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkStrLit "hi", b]

  IO.println s!"value in c: {← ppExpr (← instantiateMVars c)}"
  IO.println s!"value in d: {← ppExpr (← instantiateMVars d)}"

  let state : SavedState ← saveState
  IO.println "\nSaved state\n"

  if ← Lean.Meta.isDefEq c d then
    IO.println true
    IO.println s!"value in c: {← ppExpr (← instantiateMVars c)}"
    IO.println s!"value in d: {← ppExpr (← instantiateMVars d)}"

  restoreState state
  IO.println "\nRestored state\n"

  IO.println s!"value in c: {← ppExpr (← instantiateMVars c)}"
  IO.println s!"value in d: {← ppExpr (← instantiateMVars d)}"
