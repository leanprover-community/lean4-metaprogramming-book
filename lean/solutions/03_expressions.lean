import Lean
open Lean Meta

set_option pp.fieldNotation.generalized false

/- # Solutions -/
/- ## Expressions: Solutions -/

/- ### 1. -/
def one : Expr :=
  Expr.app (Expr.app (Expr.const `Nat.add []) (mkNatLit 1)) (mkNatLit 2)

elab "one" : term => return one

/-⋆-//-- info: Nat.add 1 2 : Nat -/
#guard_msgs in --#
#check one

/-⋆-//-- info: 3 -/
#guard_msgs in --#
#reduce one

/- ### 2. -/
def two : Expr :=
  Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]

elab "two" : term => return two

/-⋆-//-- info: Nat.add 1 2 : Nat -/
#guard_msgs in --#
#check two

/-⋆-//-- info: 3 -/
#guard_msgs in --#
#reduce two

/- ### 3. -/
def three : Expr :=
  Expr.lam `x (Expr.const `Nat [])
  (Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0])
  BinderInfo.default

elab "three" : term => return three

/-⋆-//-- info: fun x => Nat.add 1 x : Nat → Nat -/
#guard_msgs in --#
#check three

/-⋆-//-- info: 7 -/
#guard_msgs in --#
#reduce three 6

/- ### 4. -/
def four : Expr :=
  Expr.lam `a (Expr.const `Nat [])
  (
    Expr.lam `b (Expr.const `Nat [])
    (
      Expr.lam `c (Expr.const `Nat [])
      (
        Lean.mkAppN
        (Expr.const `Nat.add [])
        #[
          (Lean.mkAppN (Expr.const `Nat.mul []) #[Expr.bvar 1, Expr.bvar 2]),
          (Expr.bvar 0)
        ]
      )
      BinderInfo.default
    )
    BinderInfo.default
  )
  BinderInfo.default

elab "four" : term => return four

/-⋆-//-- info: fun a b c => Nat.add (Nat.mul b a) c : Nat → Nat → Nat → Nat -/
#guard_msgs in --#
#check four

/-⋆-//-- info: 668 -/
#guard_msgs in --#
#reduce four 666 1 2

/- ### 5. -/
def five :=
  Expr.lam `x (Expr.const `Nat [])
  (
    Expr.lam `y (Expr.const `Nat [])
    (Lean.mkAppN (Expr.const `Nat.add []) #[Expr.bvar 1, Expr.bvar 0])
    BinderInfo.default
  )
  BinderInfo.default

elab "five" : term => return five

/-⋆-//-- info: fun x y => Nat.add x y : Nat → Nat → Nat -/
#guard_msgs in --#
#check five

/-⋆-//-- info: 9 -/
#guard_msgs in --#
#reduce five 4 5

/- ### 6. -/
def six :=
  Expr.lam `x (Expr.const `String [])
  (Lean.mkAppN (Expr.const `String.append []) #[Lean.mkStrLit "Hello, ", Expr.bvar 0])
  BinderInfo.default

elab "six" : term => return six

/-⋆-//-- info: fun x => String.append "Hello, " x : String → String -/
#guard_msgs in --#
#check six

/-⋆-//-- info: "Hello, world" -/
#guard_msgs in --#
#eval six "world"

/- ### 7. -/
def seven : Expr :=
  Expr.forallE `x (Expr.sort Lean.Level.zero)
  (Expr.app (Expr.app (Expr.const `And []) (Expr.bvar 0)) (Expr.bvar 0))
  BinderInfo.default

elab "seven" : term => return seven

/-⋆-//-- info: ∀ (x : Prop), x ∧ x : Prop -/
#guard_msgs in --#
#check seven

/-⋆-//-- info: ∀ (x : Prop), x ∧ x -/
#guard_msgs in --#
#reduce seven

/- ### 8. -/
def eight : Expr :=
  Expr.forallE `notUsed
  (Expr.const `Nat []) (Expr.const `String [])
  BinderInfo.default

elab "eight" : term => return eight

/-⋆-//-- info: Nat → String : Type -/
#guard_msgs in --#
#check eight

/-⋆-//-- info: Nat → String -/
#guard_msgs in --#
#reduce eight

/- ### 9. -/
def nine : Expr :=
  Expr.lam `p (Expr.sort Lean.Level.zero)
  (
    Expr.lam `hP (Expr.bvar 0)
    (Expr.bvar 0)
    BinderInfo.default
  )
  BinderInfo.default

elab "nine" : term => return nine

/-⋆-//-- info: fun p hP => hP : ∀ (p : Prop), p → p -/
#guard_msgs in --#
#check nine

/-⋆-//-- info: fun p hP => hP -/
#guard_msgs in --#
#reduce nine

/- ### 10. -/
def ten : Expr :=
  Expr.sort (Nat.toLevel 7)

elab "ten" : term => return ten

/-⋆-//-- info: Type 6 : Type 7 -/
#guard_msgs in --#
#check ten

/-⋆-//-- info: Type 6 -/
#guard_msgs in --#
#reduce ten
