/-
# Expressions

Expressions (terms of type `Expr`) carry the data used to communicate with the
Lean kernel for core tasks such as type inference and definitional equality
checks.

In Lean, terms and types are represented by expressions. For instance, let's
consider `1` of type `Nat`. The type `Nat` is represented as a constant with the
name "Nat". And then `1` is an application of the function `Nat.succ` to the
term `Nat.zero`, so all this is represented as an application, given a constant
named "Nat.succ" and a constant named "Nat.zero".

That example gives us an idea of what we're aiming at: we use expressions to
represent all Lean terms at the meta level. Let's check the precise definition
of [`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean).
-/

import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

/-! What is each of these constructors doing?

- `bvar` is a __bound variable__. For example, the `x` in `fun x => x + 2` or
  `∑ x, x²`. This is any occurrence of a variable in an expression where there
  is a binder above it. Why is the argument a `Nat`? This is called a de Bruijn
  index and will be explained later. You can figure out the type of a bound
  variable by looking at its binder, since the binder always has the type
  information for it.
- `fvar` is a __free variable__. These are variables which are not bound by a
  binder. An example is `x` in `x + 2`. Note that you can't just look at a free
  variable `x` and tell what its type is, there needs to be a context
  which contains a declaration for `x` and its type. A free variable has an ID
  that tells you where to look for it in a `LocalContext`. In Lean 3, free
  variables were called "local constants" or "locals".
- `mvar` is a __metavariable__. There will be much more on these later, but you
  can think of it as a placeholder or a 'hole' in an expression that needs to be
  filled at a later point.
- `sort` is used for `Type u`, `Prop` etc.
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is a function application. Multiple arguments are done using _partial
  application_: `f x y ↝ app (app f x) y`.
- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`). The `b` argument
  is called the __body__. Note that you have to give the type of the variable
  you are binding.
- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`). This is
  also sometimes called a Π-type or Π-expression and is often written `∀ $n :
  $t, $b`. Note that the non-dependent arrow `α → β` is a special case of `(a :
  α) → β` where `β` doesn't depend on `a`. The `E` on the end of `forallE` is to
  distinguish it from the `forall` keyword.
- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or
  `"hello world"`. Literals help with performance: we don't want to represent
  the expression `(10000 : Nat)` as `Nat.succ $ ... $ Nat.succ Nat.zero`.
- `mdata` is just a way of storing extra information on expressions that might
  be useful, without changing the nature of the expression.
- `proj` is for projection. Suppose you have a structure such as `p : α × β`,
  rather than storing the projection `π₁ p` as `app π₁ p`, it is expressed as
  `proj Prod 0 p`. This is for efficiency reasons ([todo] find link to docstring
  explaining this).

## De Bruijn Indexes

Consider the following lambda expression `(λ f x => f x x) (λ x y => x + y) 5`,
we have to be very careful when we reduce this, because we get a clash in the
variable `x`.

To avoid variable name-clash carnage, `Expr`s use a nifty trick called
__de Bruijn indexes__. In de Bruijn indexing, each variable bound by a `lam` or
a `forallE` is converted into a number `#n`. The number says how many binders up
the `Expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments
for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction. We also
really easily check if two `Expr`s containing bound expressions are equal. This
is why the signature of the `bvar` case is `Nat → Expr` and not
`Name → Expr`.

If a de Bruijn index is too large for the number of binders preceding it, we say
it is a __loose `bvar`__; otherwise we say it is __bound__. For example, in the
expression ``lam `x _ (app #0 #1)`` the `bvar` `#0` is bound by the preceding
binder and `#1` is loose. The fact that Lean calls all de Bruijn indexes `bvar`s
("bound variables") points to an important invariant: outside of some very
low-level functions, Lean expects that expressions do not contain any loose
`bvar`s. Instead, whenever we would be tempted to introduce a loose `bvar`, we
immediately convert it into an `fvar` ("free variable"). Precisely how that
works is discussed in the next chapter.

If there are no loose `bvar`s in an expression, we say that the expression is
__closed__. The process of replacing all instances of a loose `bvar` with an
`Expr` is called __instantiation__. Going the other way is called
__abstraction__.

If you are familiar with the standard terminology around variables, Lean's
terminology may be confusing, so here's a map: Lean's "bvars" are usually called
just "variables"; Lean's "loose" is usually called "free"; and Lean's "fvars"
might be called "local hypotheses".

## Universe Levels

Some expressions involve universe levels, represented by the `Lean.Level` type.
A universe level is a natural number, a universe parameter (introduced with a
`universe` declaration), a universe metavariable or the maximum of two
universes. They are relevant for two kinds of expressions.

First, sorts are represented by `Expr.sort u`, where `u` is a `Level`. `Prop` is
`sort Level.zero`; `Type` is `sort (Level.succ Level.zero)`.

Second, universe-polymorphic constants have universe arguments. A
universe-polymorphic constant is one whose type contains universe parameters.
For example, the `List.map` function is universe-polymorphic, as the
`pp.universes` pretty-printing option shows: -/

set_option pp.universes true in
#check @List.map

/-!
The `.{u_1,u_2}` suffix after `List.map` means that `List.map` has two universe
arguments, `u_1` and `u_2`. The `.{u_1}` suffix after `List` (which is itself a
universe-polymorphic constant) means that `List` is applied to the universe
argument `u_1`, and similar for `.{u_2}`.

In fact, whenever you use a universe-polymorphic constant, you must apply it to
the correct universe arguments. This application is represented by the `List
Level` argument of `Expr.const`. When we write regular Lean code, Lean infers
the universes automatically, so we do not need think about them much. But when
we construct `Expr`s, we must be careful to apply each universe-polymorphic
constant to the right universe arguments.

## Constructing Expressions

The simplest expressions we can construct are constants. We use the `const`
constructor and give it a name and a list of universe levels. Most of our
examples only involve non-universe-polymorphic constants, in which case the list
is empty.

We also show a second form where we write the name with double backticks. This
checks that the name in fact refers to a defined constant, which is useful to
avoid typos. -/

open Lean

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

/- The double-backtick variant also resolves the given name, making it
fully-qualified. To illustrate this mechanism, here are two further examples.
The first expression, `z₁`, is unsafe: if we use it in a context where the `Nat`
namespace is not open, Lean will complain that there is no constant called
`zero` in the environment. In contrast, the second expression, `z₂`, contains
the fully-qualified name `Nat.zero` and does not have this problem. -/

open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

/- The next class of expressions we consider are function applications. These
can be built using the `app` constructor, with the first argument being an
expression for the function and the second being an expression for the argument.

Here are two examples. The first is simply a constant applied to another. The
second is a recursive definition giving an expression as a function of a natural
number. -/

def one := Expr.app (.const ``Nat.succ []) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr 
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

/-  Next we use the variant `mkAppN` which allows application with multiple
arguments. -/

def sumExpr : Nat → Nat → Expr 
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

/- As you may have noticed, we didn't show `#eval` outputs for the two last
functions. That's because the resulting expressions can grow so large that it's
hard to make sense of them.

We next use the constructor `lam` to construct a simple function which takes any
natural number `x` and returns `Nat.zero`. The argument `BinderInfo.default`
says that `x` is an explicit argument (rather than an implicit or typeclass
argument). -/

def constZero : Expr := 
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)

/-! As a more elaborate example which also involves universe levels, here is the
`Expr` that represents `List.map (λ x => Nat.add x 1) []` (broken up into
several definitions to make it somewhat readable): -/

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

/-! With a little trick (more about which in the Elaboration chapter), we can
turn our `Expr` into a Lean term, which allows us to inspect it more easily. -/

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{1, 1} Nat Nat (fun x => Nat.add x 1) (@List.nil.{1} Nat) : List.{1} Nat

#reduce mapAddOneNil
-- []

/- In the next chapter we explore the `MetaM` monad, which, among many other
things, allows us to more conveniently construct and destruct larger
expressions.

# Exercises

1. Create expression `1 + 2` with `Expr.app`.
2. Create expression `1 + 2` with `Lean.mkAppN`.
3. Create expression `λ x => 1 + x`.
4. [**De Bruijn Indexes**] We want to create expression `λ a, λ b, λ c, (b * a) + c`. Given the expression below, supersede each _ with an appropriate bound variable.

```
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
          (Lean.mkAppN (Expr.const `Nat.mul []) #[_, _]),
          (_)
        ]
      )
      BinderInfo.default
    )
    BinderInfo.default
  )
  BinderInfo.default
```

5. Create expression `λ x y => x + y`.
6. Create expression `λ x, String.append "hello, " x`.
7. Create expression `∀ x : Prop, x ∧ x`.
8. Create expression `Nat → String`. Note that both dependent arrow (`∀`) and non-dependent arrow (`→`) are both created with `Expr.forallE`.
9. Create expression `λ (p : Prop) => (λ hP : p => hP)`.
10. [**Universe levels**] Create expression `Type 6` (or, equivalently, `Sort 7`).
-/
