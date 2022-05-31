import Lean.Elab.Tactic

/-
# Tactics

We've finally come to what may be considered by many the end goal of this book.
The reason why this chapter is placed after the DSL chapter is because the
tactic mode in Lean 4 is itself a DSL.

Tactics too are Lean programs that manipulate a custom state. All tactics are,
in the end, of type `TacticM Unit`. This has the type:

```lean
-- Lean/Elab/Tactic/Basic.lean
TacticM = ReaderT Context $ StateRefT State TermElabM
```

We will start by implementing tactics that compute in `TacticM` and then we
shall see how some tactics can be implemented as macros.

## The simplest tactic: `sorry`

In this section, we wish to write a tactic that fills the proof with sorry:

```lean
theorem wrong : 1 = 2 := by
  custom_sorry

#print wrong
-- theorem wrong : 1 = 2 :=
--   sorryAx (1 = 2)
```

We begin by declaring such a tactic:
-/

elab "custom_sorry_0" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"

theorem wrong : 1 = 2 := by
  custom_sorry_0
-- 1) goal: _uniq.461
-- unsolved goals: ⊢ 1 = 2

/-
This defines a syntax extension to Lean, where we are naming the piece of syntax
`admit` as living in `tactic` syntax category. This informs the elaborator that in
the context of elaborating `tactic`s, the piece of syntax `admit` must be
elaborated as what we write to the right-hand-side of the `=>` (we fill the
`...` with the body of the tactic).

Next, we write a term in `TacticM Unit` which fills in the goal with a
`sorryAx _`. To do this, we first access the goal, and then we fill the goal in with
a `sorryAx`. We access the goal with `Lean.Elab.Tactic.getMainGoal : Tactic MVarId`,
which returns the main goal, represented as a metavariable. Recall that under
types-as-propositions, the type of our goal must be the proposition that `1 = 2`.
We check this by printing the type of `goal`.
-/

elab "custom_sorry_1" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"
  let goal_declaration ← Lean.Meta.getMVarDecl goal
  let goal_type := goal_declaration.type
  dbg_trace f!"2) goal type: {goal_type}"

theorem wrong_1 : 1 = 2 := by
  custom_sorry_1
-- 1) goal: _uniq.757
-- 2) goal type:
--      Eq.{1} Nat
--             (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
--             (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals: ⊢ 1 = 2

/-
To `sorry` the goal, we can use the helper `Lean.Elab.admitGoal`:
-/

elab "custom_sorry_2" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goal_declaration ← Lean.Meta.getMVarDecl goal
  let goal_type := goal_declaration.type
  Lean.Elab.admitGoal goal

theorem wrong_2 : 1 = 2 := by
  custom_sorry_2

#print wrong_2
-- theorem wrong_2 : 1 = 2 :=
-- sorryAx (1 = 2)

/-
And we no longer have the error `unsolved goals: ⊢ 1 = 2`.

## The `custom_trivial` tactic: Accessing Hypotheses

In this section, we will learn how to access the hypotheses to prove a goal. In
particular, we shall attempt to implement a tactic `custom_trivial`, which looks
for an exact match of the goal amongst the hypotheses, and solves the theorem if
possible.

In the example below, we expect `custom_trivial` to use `(H2 : 2 = 2)` to solve
the goal `(2 = 2)`:

```lean
theorem trivial_correct (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_trivial

#print trivial_correct
-- theorem trivial_correct : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2
```

When we do not have a matching hypothesis to the goal, we expect the tactic
`custom_trivial` to throw an error, telling us that we cannot find a hypothesis
of the type we are looking for:

```lean
theorem trivial_wrong (H1 : 1 = 1): 2 = 2 := by
  custom_trivial

#print trivial_wrong
-- tactic 'custom_trivial' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2
```

We begin by accessing the goal and the type of the goal so we know what we
are trying to prove:
-/

elab "custom_trivial_0" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"1) goal: {goal.name}"
  let goal_type ← Lean.Elab.Tactic.getMainTarget
  dbg_trace f!"2) goal type: {goal_type}"

theorem trivial_correct_0 (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_trivial_0
-- 1) goal: _uniq.638
-- 2) goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2

#print trivial_correct_0
-- theorem trivial_correct_0 : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => sorryAx (2 = 2)

theorem trivial_wrong_0 (H1 : 1 = 1): 2 = 2 := by
  custom_trivial_0
-- 1) goal: _uniq.713
-- 2) goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- ⊢ 2 = 2

#print trivial_wrong_0
-- theorem trivial_wrong : 1 = 1 → 2 = 2 :=
-- fun H1 => sorryAx (2 = 2)

/-
Next, we access the list of hypotheses, which are stored in a data structure
called `LocalContext`. This is accessed via `Lean.MonadLCtx.getLCtx`. The
`LocalContext` contains `LocalDeclaration`s, from which we can extract
information such as the name that is given to declarations (`.userName`), the
expression of the declaration (`.toExpr`). Let's write a tactic called
`list_local_decls` that prints the local declarations:
-/

elab "list_local_decls_1" : tactic => do
  let lctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM fun ldecl: Lean.LocalDecl => do
    let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
    let ldecl_name := ldecl.userName -- Find the name of the declaration.
    dbg_trace f!"+ local decl: name: {ldecl_name} | expr: {ldecl_expr}"

theorem test_list_local_decls_1 (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_1
-- + local decl: name: test_list_local_decls_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  sorry

/-
Recall that we are looking for a local declaration that has the same type as the
hypothesis. We get the type of `LocalDefinition` by calling
`Lean.Meta.inferType` on the local declaration's expression.
-/

elab "list_local_decls_2" : tactic => do
  let lctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM fun ldecl: Lean.LocalDecl => do
    let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
    let ldecl_name := ldecl.userName -- Find the name of the declaration.
    let ldecl_type ← Lean.Meta.inferType ldecl_expr -- **NEW:** Find the type.
    dbg_trace f!"+ local decl: name: {ldecl_name} | expr: {ldecl_expr} | type: {ldecl_type}"

theorem test_list_local_decls_2 (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_2
  -- + local decl: name: test_list_local_decls_2 | expr: _uniq.4263 | type: (Eq.{1} Nat ...)
  -- + local decl: name: H1 | expr: _uniq.4264 | type: Eq.{1} Nat ...)
  -- + local decl: name: H2 | expr: _uniq.4265 | type: Eq.{1} Nat ...)
  sorry

/-
We check if the type of the `LocalDefinition` is equal to the goal type with
`Lean.Meta.isExprDefEq`. See that we check if the types are equal at `eq?`, and
we print that `H1` has the same type as the goal
(`local decl[EQUAL? true]: name: H1`), and we print that `H2` does not have the
same type (`local decl[EQUAL? false]: name: H2 `):
-/

elab "list_local_decls_3" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goal_declaration ← Lean.Meta.getMVarDecl goal
  let goal_type := goal_declaration.type
  let lctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM fun ldecl: Lean.LocalDecl => do
    let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
    let ldecl_name := ldecl.userName -- Find the name of the declaration.
    let ldecl_type ← Lean.Meta.inferType ldecl_expr -- Find the type.
    let eq? ← Lean.Meta.isExprDefEq ldecl_type goal_type -- **NEW** Check if type equals goal type.
    dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {ldecl_name}"

theorem test_list_local_decls_3 (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  sorry

/-
Finally, we put all of these parts together to write a tactic that loops over
all declarations and finds one with the correct type. We loop over declarations
with `lctx.findDeclM?`. We infer the type of declarations with
`Lean.Meta.inferType`. We check that the declaration has the same type as the
goal with `Lean.Meta.isExprDefEq`:
-/

elab "custom_trivial_1" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goal_type ← Lean.Elab.Tactic.getMainTarget
  let lctx ← Lean.MonadLCtx.getLCtx
  -- Iterate over the local declarations...
  let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
    let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
    let ldecl_type ← Lean.Meta.inferType ldecl_expr -- Find the type.
    if (← Lean.Meta.isExprDefEq ldecl_type goal_type) -- Check if type equals goal type.
    then return Option.some ldecl_expr -- If equal, success!
    else return Option.none -- Not found.
  dbg_trace f!"matching_expr: {option_matching_expr}"

theorem trivial_correct_1 (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_trivial_1
-- matching_expr: some _uniq.6241
  sorry

#print trivial_correct_1
-- theorem trivial_correct_1 : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => sorryAx (2 = 2) false

theorem trivial_wrong_1 (H1 : 1 = 1): 2 = 2 := by
  custom_trivial_1
-- matching_expr: none
  sorry

#print trivial_wrong_1
-- theorem trivial_wrong_1 : 1 = 1 → 2 = 2 :=
-- fun H1 => sorryAx (2 = 2) false

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

elab "custom_trivial_2" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let goal_type ← Lean.Elab.Tactic.getMainTarget
  let lctx ← Lean.MonadLCtx.getLCtx
  let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
    let ldecl_expr := ldecl.toExpr
    let ldecl_type ← Lean.Meta.inferType ldecl_expr
    if ← Lean.Meta.isExprDefEq ldecl_type goal_type
      then return Option.some ldecl_expr
      else return Option.none
  match option_matching_expr with
  | some e => Lean.Elab.Tactic.closeMainGoal e
  | none => do
    Lean.Meta.throwTacticEx `custom_trivial_2 goal (m!"unable to find matching hypothesis of type ({goal_type})")

theorem trivial_correct_2 (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_trivial_2

#print trivial_correct_2
-- theorem trivial_correct_2 : 1 = 1 → 2 = 2 → 2 = 2 :=
-- fun H1 H2 => H2

theorem trivial_wrong_2 (H1 : 1 = 1): 2 = 2 := by
  custom_trivial_2
-- tactic 'custom_trivial_2' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2

/- ## Tweaking the context
Until now, we've only performed read-like operations with the context. But what
if we want to change it?

In this section we will see how to change the order of goals and how to add
content to it (new hypotheses).

For the first task, we can use `Lean.Elab.Tactic.getGoals` and
`Lean.Elab.Tactic.setGoals`:
-/

elab "reverse_goals" : tactic => do
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

/-
Now let's try to simulate a `let` and a `have`. For this task, first we will
need to use `Lean.Elab.Tactic.withMainContext`, which can run commands taking
into consideration the entire goal state. This is important because if the user
has some `n : Nat` in the context and wants to do `custom_have h : n = n := rfl`
then our tactic will need to elaborate the type `n = n` while knowing what `n`
is.

Then, after elaborating our terms, we will need to use the helper function
`Lean.Elab.Tactic.liftMetaTactic`, which allows us to run computations in
`MetaM` while also giving us the goal `MVarId` for us to play with. In the end
of our computation, `liftMetaTactic` expects us to return a `List MVarId` as the
resulting list of goals.

The only substantial difference between `custom_let` and `custom_have` is that
the former uses `Lean.Meta.define` and the later uses `Lean.Meta.assert`:
-/

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← Lean.Meta.define mvarId n.getId t v
      let (_, mvarIdNew) ← Lean.Meta.intro1P mvarIdNew
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← Lean.Meta.assert mvarId n.getId t v
      let (_, mvarIdNew) ← Lean.Meta.intro1P mvarIdNew
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  sorry

/-
## Tactics by Macro Expansion

Just like many other parts of the Lean 4 infrastructure, tactics too can be
declared by lightweight macro expansion.

For example, we build an example of a `custom_sorry_macro` that elaborates into
a `sorry`. We write this as a macro expansion, which expands the piece of syntax
`custom_sorry_macro` into the piece of syntax `sorry`:
-/

macro "custom_sorry" : tactic => `(tactic| sorry)

theorem test_sorry_custom_macro: 1 = 42 := by
  custom_sorry

#print test_sorry_custom_macro
-- theorem test_sorry_custom_macro : 1 = 42 :=
--   sorryAx (1 = 42) false

/-
### Implementing `trivial`: Extensible Tactics by Macro Expansion

As more complex examples, we can write a tactic such as `custom_trivial`, which is initially left
completely unimplemented, and can be extended with more tactics. We start by simply declaring
the tactic with no implementation:
-/

syntax "custom_trivial" : tactic

theorem test_custom_trivial_macro_0: 42 = 42 := by
  custom_trivial
-- tactic 'tacticCustom_trivial' has not been implemented
  sorry

/-
We will now add the `rfl` tactic into `custom_trivial`, which will allow us to
prove the previous theorem
-/

macro_rules
| `(tactic| custom_trivial) => `(tactic| rfl)

theorem test_custom_trivial_macro_1: 42 = 42 := by
   custom_trivial
-- Goals accomplished 🎉

/-
We can now try a harder problem, that cannot be immediately dispatched by `rfl`:
-/

theorem test_custom_trivial_macro_2: 43 = 43 ∧ 42 = 42:= by
  custom_trivial
-- tactic 'rfl' failed, equality expected{indentExpr targetType}
-- ⊢ 43 = 43 ∧ 42 = 42

/-
We extend the `custom_trivial` tactic with a tactic that tries to break `And`
down with `apply And.intro`, and then (recursively (!)) applies `custom_trivial`
to the two cases with `(<;> trivial)` to solve the generated subcases `43 = 43`,
`42 = 42`.
-/

macro_rules
| `(tactic| custom_trivial) => `(tactic| apply And.intro <;> custom_trivial)

/-
The above declaration uses `<;>` which is a *tactic combinator*. Here, `a <;> b`
means "run tactic `a`, and apply "b" to each goal after running `a`". Thus,
`And.intro <;> custom_trivial` means "run `And.intro`, and then run
`custom_trivial` on each goal". We test it out on our previous theorem and see
that we dispatch the theorem.
-/

theorem test_custom_trivial_macro_3 : 43 = 43 ∧ 42 = 42 := by
  custom_trivial
-- Goals accomplished 🎉

/-
In summary, we declared an extensible tactic called `custom_trivial`. It
initially had no elaboration at all. We added the `rfl` as an elaboration of
`custom_trivial`, which allowed it to solve the goal `42 = 42`. We then tried a
harder theorem, `43 = 43 ∧ 42 = 42` which `custom_trivial` was unable to solve.
We were then able to enrich `custom_trivial` to split "and" with `And.intro`, and
also *recursively* call `custom_trivial` in the two subcases.

## Implementing `<;>`: Tactic Combinators by Macro Expansion

Recall that in the previous section, we say that `a <;> b` meant "run `a`, and
then run `b` for all goals". In fact, `<;>` itself is a tactic combinator. In
this section, we will implement the syntax `a and_then b` which will stand for
"run `a`, and then run `b` for all goals".
-/

-- 1. We declare the syntax `and_then`
syntax tactic " and_then " tactic : tactic

-- 2. We write the expander that expands the tactic
--    into running `a`, and then running `b` on all goals.
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
## FAQ

In this section, we collect common patterns that are used during writing tactics,
to make it easy to find common patterns.

**Q: How do I use goals?**

A: Goals are represented as metavariables. The module `Lean.Elab.Tactic.Basic`
has many functions to add new goals, switch goals, etc.

**Q: How do I get the main goal?**

A: Use `Lean.Elab.Tactic.getMainGoal`.
-/

elab "faq_main_goal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  dbg_trace f!"goal: {goal.name}"

theorem test_faq_main_goal: 1 = 1 := by
  faq_main_goal
-- goal: _uniq.9298
  sorry

/-
**Q: How do I get the list of goals?**

A: Use `getGoals`.
-/

elab "faq_get_goals" : tactic => do
  let goals ← Lean.Elab.Tactic.getGoals
  goals.forM $ fun goal => do
    let goal_type ← Lean.Meta.getMVarType goal
    dbg_trace f!"goal: {goal.name} | type: {goal_type}"

theorem test_faq_get_goals (b: Bool): b = true := by
  cases b;
  faq_get_goals
-- goal: _uniq.10067 | type: Eq.{1} Bool Bool.false Bool.true
-- goal: _uniq.10078 | type: Eq.{1} Bool Bool.true Bool.true
  sorry
  sorry

/-
**Q: How do I get the current hypotheses for a goal?**

A: Use `Lean.MonadLCtx.getLCtx` which provides the local context, and then
iterate on the `LocalDeclaration`s of the `LocalContext` with accessors such as
`foldlM` and `forM`.
-/

elab "faq_get_hypotheses" : tactic => do
  let lctx ← Lean.MonadLCtx.getLCtx -- get the local context.
  lctx.forM (fun (ldecl: Lean.LocalDecl) => do
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_type := ldecl.type -- Find the expression of the declaration.
      let ldecl_name := ldecl.userName -- Find the name of the declaration.
      dbg_trace f!" local decl: name: {ldecl_name} | expr: {ldecl_expr} | type: {ldecl_type}"
  )

theorem test_faq_get_hypotheses (H1 : 1 = 1) (H2 : 2 = 2): 3 = 3 := by
  faq_get_hypotheses
  -- local decl: name: test_faq_get_hypotheses | expr: _uniq.10814 | type: ...
  -- local decl: name: H1 | expr: _uniq.10815 | type: ...
  -- local decl: name: H2 | expr: _uniq.10816 | type: ...
  sorry

/-
**Q: How do I evaluate a tactic?**

A: Use `Lean.Elab.Tactic.evalTactic: Syntax → TacticM Unit` which evaluates a
given tactic syntax. One can create tactic syntax using the macro
`(tactic| ⋯)`.

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

elab "faq_throw_error" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  Lean.Meta.throwTacticEx `faq_throw_error goal "throwing an error at the current goal"

theorem test_faq_throw_error (b : Bool): b = true := by
  cases b;
  faq_throw_error
  -- case true
  -- ⊢ true = true
  -- tactic 'faq_throw_error' failed, throwing an error at the current goal
  -- case false
  -- ⊢ false = true

/-
**Q: What is the difference between `Lean.Elab.Tactic.*` and `Lean.Meta.Tactic.*`?**

A: `Lean.Meta.Tactic.*` contains low level code that uses the `Meta` monad to
implement basic features such as rewriting. `Lean.Elab.Tactic.*` contains
high-level code that connects the low level development in `Lean.Meta` to the
tactic infrastructure and the parsing front-end.
-/
