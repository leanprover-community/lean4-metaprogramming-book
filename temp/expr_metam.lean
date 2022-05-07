import Lean

open Lean Meta

/- As the code above was rather complicated, it is better to check it. A
convenient way to do this is to use an _elaborator_ to assign the expression to
a constant and then check it. We will explain elaborators in a future chapter.

One can construct _let-expressions_ in a manner similar to λ-expressions. We
use `withLetDecl` to introduce into the context a let declaration with given
name, type, value. We apply this to a _continuation_, which is a function with
variable corresponding to the one defined in the `let` statement. The
continuation should return an expression relative to the `let` declaration --
this is done using the `mkLetFVars` function. -/

elab "two!" : term => do
  let z := Lean.mkConst `Nat.zero
  let ty := Lean.mkConst `Nat
  withLetDecl `n ty z fun x => do
    let one ← mkAppM ``Nat.succ #[x]
    let two ← mkAppM ``Nat.add #[one, one]
    let e ← mkLetFVars #[x] two
    return e

#eval (two! : Nat) -- 2

/-!
## Matching on expressions

Often we wish to construct expressions depending on the nature of other
expressions. To do this, we can directly match given expressions using the
inductive nature of `Expr`. However, it is often more convenient to use helpers
that lean provides to recognize expressions of specific forms.

We consider one such example: given an equality type `lhs = rhs`, we construct
the type `rhs = lhs`. This is done by matching on the expression using
`Expr.eq?`, which returns `some (α, lhs, rhs)` if the expression is an equality,
with `α` the type of `lhs` (and `rhs`), and `none` otherwise.

Note that the elaborator for testing is a little more complicated than the
previous cases. Details of such elaborators will be discussed in a future
chapter.
-/

def flipEquality (type: Expr): MetaM Expr := do
  match type.eq? with
  | some (α, lhs, rhs) =>
    mkEq rhs lhs
  | _ => throwError "can only flip equality types"

open Elab Term in
elab "flipEq!" ty:term : term => do
  let ty ← elabType ty
  let e ← flipEquality ty
  return e

#check flipEq! (5 = 3) -- 3 = 5 : Prop
