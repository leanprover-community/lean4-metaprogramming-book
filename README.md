# A Lean 4 Metaprogramming Book

Authors: Arthur Paulino, Damiano Testa, Edward Ayers, Evgenia Karunus, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

A PDF is [available here for download](../../releases/download/latest/Metaprogramming.in.Lean.4.pdf) (and is rebuilt on each change).

* Main
    1. [Introduction](md/main/01_intro.md)
    2. [Overview](md/main/02_overview.md)
    3. [Expressions](md/main/03_expressions.md)
    4. [`MetaM`](md/main/04_metam.md)
    5. [`Syntax`](md/main/05_syntax.md)
    6. [Macros](md/main/06_macros.md)
    7. [Elaboration](md/main/07_elaboration.md)
    8. [DSLs](md/main/08_dsls.md)
    9. [Tactics](md/main/09_tactics.md)
    10. [Cheat sheet](md/main/10_cheat-sheet.md)
    1. [Options](md/extra/01_options.md)
    2. [Attributes](md/extra/02_attributes.md)
    3. [Pretty Printing](md/extra/03_pretty-printing.md)
* Solutions to exercises
    1. Introduction
    2. Overview
    3. [Expressions](md/solutions/03_expressions.md)
    4. [`MetaM`](md/solutions/04_metam.md)
    5. [`Syntax`](md/solutions/05_syntax.md)
    6. Macros
    7. [Elaboration](md/solutions/07_elaboration.md)
    8. DSLs
    9. [Tactics](md/solutions/09_tactics.md)

Sources to extract material from:
* [Material written by Ed](https://github.com/leanprover-community/mathlib4/blob/tutorial/docs/metaprogramming/02_metavariables.md)

## Contributing

The markdown files are generated automatically via [lean2md](https://github.com/arthurpaulino/lean2md).
Thus, if you're going to write or fix content for the book, please do so in the original Lean files inside the [lean](lean) directory.

**Important**: since `lean2md` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.

### Building the markdown files

This is not required, but if you want to build the markdown files, you can do so by running `lake run build`.
It requires having Python installed, as well as the `lean2md` package.

Or, if you have [viper](https://github.com/arthurpaulino/viper) installed and a linked environment that has `lean2md`, you can call `lake run viper_build`.
