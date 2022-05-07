# A Lean 4 Metaprogramming Book

Authors: Arthur Paulino, Edward Ayers, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

* [Introduction](md/intro.md)
* [Expressions](md/expressions.md)
* [`MetaM`](md/metam.md)
* [`Syntax`](md/syntax.md)
* [Elaboration](md/elaboration.md)
* [Macros](md/macros.md)
* [DSLs](md/monad-stacks.md)
* [Tactics](md/tactics.md)

Sources to extract material from:
* [Material written by Ed](https://github.com/leanprover-community/mathlib4/blob/tutorial/docs/metaprogramming/02_metavariables.md)

## Collaborating

The markdown files are generated automatically via
[lean2md](https://github.com/arthurpaulino/lean2md). Thus, if you're going to
write or fix content for the book, please do so in the original Lean files
inside the [lean](lean) directory.

**Important**: since `lean2md` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.
