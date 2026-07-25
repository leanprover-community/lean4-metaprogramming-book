import Lean
open Lean Meta

/- # Solutions -/
/- ## Expressions: Solutions -/

/- ### 1. -/
def one : Expr :=
  Expr.app (Expr.app (Expr.const `Nat.add []) (mkNatLit 1)) (mkNatLit 2)

elab "one" : term => return one
/--
info: Nat.add 1 2 : Nat
-/
#guard_msgs in --#
#check one  -- Nat.add 1 2 : Nat
#reduce one -- 3

/- ### 2. -/
def two : Expr :=
  Lean.mkAppN (Expr.const `Nat.add []) #[mkNatLit 1, mkNatLit 2]

elab "two" : term => return two
/--
info: Nat.add 1 2 : Nat
-/
#guard_msgs in --#
#check two  -- Nat.add 1 2 : Nat
#reduce two -- 3

/- ### 3. -/
def three : Expr :=
  Expr.lam `x (Expr.const `Nat [])
  (Lean.mkAppN (Expr.const `Nat.add []) #[Lean.mkNatLit 1, Expr.bvar 0])
  BinderInfo.default

elab "three" : term => return three
/--
info: fun x => Nat.add 1 x : Nat → Nat
-/
#guard_msgs in --#
#check three    -- fun x => Nat.add 1 x : Nat → Nat
#reduce three 6 -- 7

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
/--
info: fun a b c => (b.mul a).add c : Nat → Nat → Nat → Nat
-/
#guard_msgs in --#
#check four -- fun a b c => Nat.add (Nat.mul b a) c : Nat → Nat → Nat → Nat
#reduce four 666 1 2 -- 668

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
/--
info: fun x y => x.add y : Nat → Nat → Nat
-/
#guard_msgs in --#
#check five      -- fun x y => Nat.add x y : Nat → Nat → Nat
#reduce five 4 5 -- 9

/- ### 6. -/
def six :=
  Expr.lam `x (Expr.const `String [])
  (Lean.mkAppN (Expr.const `String.append []) #[Lean.mkStrLit "Hello, ", Expr.bvar 0])
  BinderInfo.default

elab "six" : term => return six
/--
info: fun x => "Hello, ".append x : String → String
-/
#guard_msgs in --#
#check six        -- fun x => String.append "Hello, " x : String → String
#guard reprStr (six "world") == "\"Hello, world\"" -- "Hello, world"

/- ### 7. -/
def seven : Expr :=
  Expr.forallE `x (Expr.sort Lean.Level.zero)
  (Expr.app (Expr.app (Expr.const `And []) (Expr.bvar 0)) (Expr.bvar 0))
  BinderInfo.default

elab "seven" : term => return seven
/--
info: ∀ (x : Prop), x ∧ x : Prop
-/
#guard_msgs in --#
#check seven  -- ∀ (x : Prop), x ∧ x : Prop
#reduce seven -- ∀ (x : Prop), x ∧ x

/- ### 8. -/
def eight : Expr :=
  Expr.forallE `notUsed
  (Expr.const `Nat []) (Expr.const `String [])
  BinderInfo.default

elab "eight" : term => return eight
/--
info: Nat → String : Type
-/
#guard_msgs in --#
#check eight  -- Nat → String : Type
#reduce eight -- Nat → String

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
/--
info: fun p hP => hP : ∀ (p : Prop), p → p
-/
#guard_msgs in --#
#check nine  -- fun p hP => hP : ∀ (p : Prop), p → p
#reduce nine -- fun p hP => hP

/- ### 10. -/
def ten : Expr :=
  Expr.sort (Nat.toLevel 7)

elab "ten" : term => return ten
/--
info: Type 6 : Type 7
-/
#guard_msgs in --#
#check ten  -- Type 6 : Type 7
#reduce ten -- Type 6
