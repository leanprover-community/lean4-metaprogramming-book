# Datatypes

--todo
* MVarId

## Names

A name is just a list of strings and numbers `string1.3.string2.string3.55`. We
use a list of strings because then we can have things like `namespaces`. See
https://leanprover.github.io/lean4/doc/organization.html

```lean
namespace Playground

inductive Name where
  | anonymous : Name             -- the empty name
  | str : Name → String → Name -- append a string to the name
  | num : Name → Nat → Name    -- append a number to the name

end Playground
```

We can use backticks `` ` `` to access names from Lean objects.
* `` `my.name`` is the way to refer to a name. It is essentially a form of
string quoting; no checks are done besides parsing dots into namespaced names
* ``` ``some ``` does name resolution at parse time, so it expands to
`` `option.some``. It will error if the given name doesn't exist.

When you write `namespace x ... end x` in your document, this is the same as
using `open x` and prepending `x.` to all of your declarations within the
`namespace/end` block.

## Type Universes

To avoid paradoxes (think; "does the type of all types contain itself?"), we
have an infinite hierarchy of type universes. This is one of the more confusing
things for newcomers but it can be ignored most of the time.

You can think of a universe level as just a natural number. But remember that
these numbers are at the meta level. So you can't perform induction on them etc.
That means that the numbers are used to talk about things within Lean, rather
than being an object of study itself. Here is a (simplified) definition, given
in `library/init/meta/level.lean` in the Lean codebase with my comments

```lean
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
```

Universes can be thought of as a tedious-but-necessary bookkeeping exerciseto stop the paradoxes and Lean does a good job of hiding them from the user in
most circumstances.
