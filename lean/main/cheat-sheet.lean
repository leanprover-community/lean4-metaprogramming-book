/-
#  Lean4 Cheat-sheet

##  Extracting information

* Extract the goal: `Lean.Elab.Tactic.getMainGoal`

  Use as `let goal ← Lean.Elab.Tactic.getMainGoal`
* Extract the declaration out of a meta-variable: `Lean.Meta.getMVarDecl mvar`
  when `mvar : Lean.MVarId` is in context.
  For instance, `mvar` could be the goal extracted using `getMainGoal`
* Extract the type of a meta-variable: `Lean.MetavarDecl.type mvdecl`
  when `mvdecl : Lean.MetavarDecl` is in context.
* Extract the type of the main goal: `Lean.Elab.Tactic.getMainTarget`

  Use as `let goal_type ← Lean.Elab.Tactic.getMainTarget`

  Achieves the same as 
```lean
let goal ← Lean.Elab.Tactic.getMainGoal
let goal_decl ← Lean.Meta.getMVarDecl goal
let goal_type := goal_decl.type
```
* Extract local context: `Lean.MonadLCtx.getLCtx`

  Use as `let lctx ← Lean.MonadLCtx.getLCtx`
* Extract the name of a declaration: `Lean.LocalDecl.userName ldecl`
  when `ldecl : Lean.LocalDecl` is in context
* Extract the type of an expression: `Lean.Meta.inferType expr`
  when `expr : Lean.Expr` is an expression in context

  Use as `let expr_type ← Lean.Meta.inferType expr`

##  Playing around with expressions

* Convert a declaration into an expression: `Lean.LocalDecl.toExpr`
  
  Use as `ldecl.toExpr`, when `ldecl : Lean.LocalDecl` is in context
  
  For instance, `ldecl` could be `let ldecl ← Lean.MonadLCtx.getLCtx`
* Check whether two expressions are definitionally equal: `Lean.Meta.isExprDefEq ex1 ex2`
  when `ex1 ex2 : Lean.Expr` are in context. Returns a `Lean.MetaM Bool`
  
  `isDefEq ex1 ex2` appears to be a synonym
* Close a goal: `Lean.Elab.Tactic.closeMainGoal expr`
  when `expr : Lean.Expr` is in context

##  Further commands

* meta-sorry: `Lean.Elab.admitGoal goal`, when `goal : Lean.MVarId` is the current goal

##  Printing and errors

* Print a message: `dbg_trace f!"1) goal: {goal.name}"`
  
  Use as `dbg_trace f!"1) goal: {goal.name}"`
  when `goal : Lean.MVarId` is in context.
  
  What is the role of `f!`?  I see no difference using
  `dbg_trace "text"`, `dbg_trace f!"text"`, `dbg_trace s!"text"`
  Other characters seem to not be defined.
* Throw an error: `Lean.Meta.throwTacticEx name mvar message_data`
  where `name : Lean.Name` is the name of a tactic and `mvar` contains error data.
  
  Use as `Lean.Meta.throwTacticEx `tac goal (m!"unable to find matching hypothesis of type ({goal_type})")`
  where the `m!` formatting builds a `MessageData` for better printing of terms

TODO: Add?
* Lean.LocalContext.forM
* Lean.LocalContext.findDeclM?
-/
