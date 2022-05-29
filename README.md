# A Lean 4 Metaprogramming Book

Authors: Arthur Paulino, Edward Ayers, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

* Main
    1. [Introduction](md/main/intro.md)
    2. [Expressions](md/main/expressions.md)
    3. [`MetaM`](md/main/metam.md)
    4. [`Syntax`](md/main/syntax.md)
    5. [Macros](md/main/macros.md)
    6. [Elaboration](md/main/elaboration.md)
    7. [DSLs](md/main/dsls.md)
    8. [Tactics](md/main/tactics.md)
* Extra
    1. [Options](md/extra/options.md)
    2. [Attributes](md/extra/attributes.md)
    1. [Pretty Printing](md/extra/pretty-printing.md)

Sources to extract material from:
* [Material written by Ed](https://github.com/leanprover-community/mathlib4/blob/tutorial/docs/metaprogramming/02_metavariables.md)

## Collaborating

The markdown files are generated automatically via
[lean2md](https://github.com/arthurpaulino/lean2md). Thus, if you're going to
write or fix content for the book, please do so in the original Lean files
inside the [lean](lean) directory.

To build the markdown files, please run `lake script run build`

**Important**: since `lean2md` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.
