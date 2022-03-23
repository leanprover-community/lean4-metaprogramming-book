/-!
# Datatypes

> The pieces of information that Lean uses for metaprogramming

--todo
* smart Expr constructors
* locally nameless representation; `forallTelescope` and friends
* implicit arguments, app builder (`mkAppM` etc.)
* matching on expressions
* normalisation, transparency
* discrimination trees
* unification

## Expressions

The Lean type `Expr` is just an inductive datatype that you can look at like
any other. Let me give a cut down version of the one given in
[Lean/Expr.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
where I throw away some details to add back in later.
-/

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                       -- bound variables
  | fvar    : FVarId → Expr                    -- free variables
  | mvar    : MVarId → Expr                    -- meta variables
  | sort    : Level → Expr                     -- Sort
  | const   : Name → List Level → Expr         -- constants
  | app     : Expr → Expr → Expr               -- application
  | lam     : Name → Expr → Expr → Expr        -- lambda abstraction
  | forallE : Name → Expr → Expr → Expr        -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                   -- literals
  | mdata   : MData → Expr → Expr              -- metadata
  | proj    : Name → Nat → Expr → Expr         -- projection

end Playground

/-! We can represent any Lean term using the above definition.
Multiple arguments are done using _partial application_:
`f x y ↝ app (app f x) y`.

What is each of these constructors doing?

- `bvar` is a __bound variable__. For example, the `x` in `fun x => x + 2` or
  `∑ x, x²`. This is any occurrence of a variable in an expression where there
  is a binder above it. Why is the argument a `Nat`? This is called a de-Bruijn
  index and is explained [here](#de-bruijn-indexes). You can figure out the type
  of a bound variable by looking at its binder, since the binder always has the
  type information for it.
- `fvar` is a __free variable__. These are variables which are not bound by a
  binder. An example is `x` in `x + 2`. Note that you can't just look at a free
  variable `x` and tell what its type is, you need there to be a context
  (denoted `Γ` from the previous section) which contains an declaration for `x`
  and its type.
  A free variable has an ID that tells you where to look for it in a
  `LocalContext` In Lean 3, free variables were called "local constants" or
  "locals".
- `mvar` is a __metavariable__. There will be much more on these later, but you
  can think of it as a placeholder or a 'hole' in an expression that needs to be
  filled at a later point.
- `sort` is used for `Type u`, `Prop`. The meaning of `Level` is discussed
  [here](#type-universes).
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is function application.
- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`). The `b` argument
  is called the __body__. Note that you have to give the type of the variable
  you are binding.
- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`). This is
  also sometimes called a Π-type or Π-expression. Note that the non-dependent
  arrow `α → β` is a special case of `(a : α) → β` where `β` doesn't depend on
  `a`. The `E` on the end of `forallE` is to distinguish it from the `forall`
  keyword.
- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or
  `"hello world"`. These are not strictly necessary for the kernel, but they are
  kept mainly for convenience. (Ie in Lean 3, there were a load of tricks needed
  to store `11234 : Nat` as something more efficient than
  `succ $ succ $ succ ... $ succ zero`)
- `mdata` is just a way of storing extra information on expressions that might
  be useful, without changing the nature of the expression.
- `proj` is for projection. Suppose you have a structure such as `p : α × β`,
  rather that storing the projection `π₁ p` as `app π₁ p`, it is expressed as
  `proj Prod 0 p`. This is for efficiency reasons ([todo] find link to docstring
  explaining this).

### Expression Data

If you look at the file where `Expr` is defined, you will see that every
constructor also has a `Data` argument to it that I have omitted above. This
Data field contains some extra cached information about the expression that is
useful for speeding up some common operations.
These are things like; a hash of the `Expr`, whether or not the `Expr` contains
free variables, metavariables or bound variables and also it is where the
`BinderInfo` is stored for `forallE` and `lam`.

This data param means that you should _never_ construct instances of `Expr`
directly using the `Expr` constructors but instead use the helper methods
(`mkLambda`, `mkApp` etc) that compute `Data` for you.

## de-Bruijn Indexes

Consider the following lambda expression ` (λ f x => f x x) (λ x y => x + y) 5`,
we have to be very careful when we reduce this, because we get a clash in the
variable `x`.
To avoid variable name-clash carnage, `Expr`s use a nifty trick called
__de-Bruijn indexes__. In de-Bruijn indexing, each variable bound by a `lam` or
a `forallE` is converted into a number `#n`. The number says how many binders up
the `Expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments
for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction. We also
really easily check if two `Expr`s containing bound expressions are equal.

This is why the signature of the `bvar` case is `Nat → Expr` and not
`Name → Expr`. If in our `Expr`, all `bvar`s are bound, we say that the `Expr`
is __closed__. The process of replacing all instances of an unbound `bvar` with
an `Expr` is called __instantiation__. Going the other way is called
__abstraction__.

## Type Universes

To avoid paradoxes (think; "does the type of all types contain itself?"), we
have an infinite hierarchy of type universes. This is one of the more confusing
things for newcomers but it can be ignored most of the time.

You can think of a universe level as just a natural number. But remember that
these numbers are at the meta level. So you can't perform induction on them etc.
That means that the numbers are used to talk about things within Lean, rather
than being an object of study itself. Here is a (simplified) definition, given
in `library/init/meta/level.lean` in the Lean codebase with my comments

-/

namespace Playground

inductive Level where
   -- The zeroth universe. This is also called `Prop`.
  | zero   : Level
  -- The successor of the given universe
  | succ   : Level → Level
  -- The maximum of the given two universes
  | max    : Level → Level → Level
  -- Same as `max`, except that `imax u zero` reduces to `zero`.
  -- This is used to make sure `(x : α) → t` is a `Prop` if `t` is too.
  | imax   : Level → Level → Level
  -- A named parameter universe. Eg, at the beginning of a Lean
  -- file you would write `universe u`. `u` is a parameter.
  | param  : Name → Level
  -- A metavariable, to be explained later.
  -- It is a placeholder universe that Lean is expected to guess later.
  | mvar   : MVarId → Level

end Playground

/-!

Universes can be thought of as a tedious-but-necessary bookkeeping exercise to
stop the paradoxes and Lean does a good job of hiding them from the user in most
circumstances.
Because of this, I will try my hardest to omit details about type universes for
the rest of this document.

## Names

A name is just a list of strings and numbers `string1.3.string2.string3.55`. We
use a list of strings because then we can have things like `namespaces`. See
https://leanprover.github.io/lean4/doc/organization.html
-/

namespace Playground

inductive Name where
  | anonymous : Name             -- the empty name
  | str : Name → String → Name -- append a string to the name
  | num : Name → Nat → Name    -- append a number to the name

end Playground

/-! We can use backticks `` ` `` to access names from Lean objects.

* `` `my.name`` is the way to refer to a name. It is essentially a form of
string quoting; no checks are done besides parsing dots into namespaced names
* ``` ``some ``` does name resolution at parse time, so it expands to
`` `option.some``. It will error if the given name doesn't exist.

When you write `namespace x ... end x` in your document, this is the same as
using `open x` and prepending `x.` to all of your declarations within the
`namespace/end` block.
-/
