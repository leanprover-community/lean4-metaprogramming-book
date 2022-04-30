# A Lean 4 Metaprogramming Book

Authors: Arthur Paulino, Edward Ayers, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

* [Introduction](md/intro.md)
* [Expressions](md/expressions.md)
* [Monad stacks](md/monad-stacks.md)
* [`CoreM`](md/corem.md)
* [`MetaM`](md/metam.md)
* [`Syntax`](md/syntax.md)
* [`MacroM`](md/macrom.md)
* [Elaboration](md/elaboration.md)
* [`TacticM`](md/tacticm.md)
* [Delaboration](md/delaboration.md)
* [Environment extensions](md/env-extensions.md)
* [Attributes](md/attributes.md)
* [Options](md/options.md)
* [Initialization](md/initialization.md)

Sources to extract material from:
* [Metavariables by Ed](https://github.com/leanprover-community/mathlib4/blob/tutorial/docs/metaprogramming/02_metavariables.md)

## Collaborating

The markdown files are generated automatically via
[lean2md](https://github.com/arthurpaulino/lean2md). Thus, if you're going to
write or fix content for the book, please do so in the original Lean files
inside the [lean](lean) directory.

**Important**: since `lean2md` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.
