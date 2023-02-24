import Lean
open Lean Elab Command Term Meta

/- ## Elaboration: Solutions -/

/- ### 1. -/

elab n:term "♥" a:"♥"? b:"♥"? : term => do
  let nExpr : Expr ← elabTermEnsuringType n (mkConst `Nat)
  if let some a := a then
    if let some b := b then
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 3)
    else
      return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 2)
  else
    return Expr.app (Expr.app (Expr.const `Nat.add []) nExpr) (mkNatLit 1)

#eval 7 ♥ -- 8
#eval 7 ♥♥ -- 9
#eval 7 ♥♥♥ -- 10

/- ### 2. -/

-- a) using `syntax` + `@[command_elab alias] def elabOurAlias : CommandElab`
syntax (name := aliasA) (docComment)? "aliasA " ident " ← " ident* : command

@[command_elab «aliasA»]
def elabOurAlias : CommandElab := λ stx =>
  match stx with
  | `(aliasA $x:ident ← $ys:ident*) =>
    for y in ys do
      Lean.logInfo y
  | _ =>
    throwUnsupportedSyntax

aliasA hi.hello ← d.d w.w nnn

-- b) using `syntax` + `elab_rules`.
syntax (name := aliasB) (docComment)? "aliasB " ident " ← " ident* : command

elab_rules : command
  | `(command | aliasB $m:ident ← $ys:ident*) =>
    for y in ys do
      Lean.logInfo y

aliasB hi.hello ← d.d w.w nnn

-- c) using `elab`
elab "aliasC " x:ident " ← " ys:ident* : command =>
  for y in ys do
    Lean.logInfo y

aliasC hi.hello ← d.d w.w nnn

/- ### 3. -/

open Parser.Tactic

-- a) using `syntax` + `@[tactic nthRewrite] def elabNthRewrite : Lean.Elab.Tactic.Tactic`.
syntax (name := nthRewriteA) "nth_rewriteA " (config)? num rwRuleSeq (ppSpace location)? : tactic

@[tactic nthRewriteA] def elabNthRewrite : Lean.Elab.Tactic.Tactic := λ stx => do
  match stx with
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteA $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"
  | _ =>
    throwUnsupportedSyntax

-- b) using `syntax` + `elab_rules`.
syntax (name := nthRewriteB) "nth_rewriteB " (config)? num rwRuleSeq (ppSpace location)? : tactic

elab_rules (kind := nthRewriteB) : tactic
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules $_loc) =>
    Lean.logInfo "rewrite location!"
  | `(tactic| nth_rewriteB $[$cfg]? $n $rules) =>
    Lean.logInfo "rewrite target!"

-- c) using `elab`.
elab "nth_rewriteC " (config)? num rwRuleSeq loc:(ppSpace location)? : tactic =>
  if let some loc := loc then
    Lean.logInfo "rewrite location!"
  else
    Lean.logInfo "rewrite target!"

example : 2 + 2 = 4 := by
  nth_rewriteC 2 [← add_zero] at h
  nth_rewriteC 2 [← add_zero]
  sorry
