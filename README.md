# A Lean 4 Metaprogramming Book

Authors: Arthur Paulino, Damiano Testa, Edward Ayers, Henrik Böving, Jannis Limperg, Siddhartha Gadgil, Siddharth Bhat

A PDF is [available here for download](../../releases/download/latest/Metaprogramming.in.Lean.4.pdf) (and is rebuilt on each change).

* Main
    1. [Introduction](md/main/intro.md)
    2. [Expressions](md/main/expressions.md)
    3. [`MetaM`](md/main/metam.md)
    4. [`Syntax`](md/main/syntax.md)
    5. [Macros](md/main/macros.md)
    6. [Elaboration](md/main/elaboration.md)
    7. [DSLs](md/main/dsls.md)
    8. [Tactics](md/main/tactics.md)
    9. [Cheat sheet](md/main/cheat-sheet.md)
* Extra
    1. [Options](md/extra/options.md)
    2. [Attributes](md/extra/attributes.md)
    1. [Pretty Printing](md/extra/pretty-printing.md)

Sources to extract material from:
* [Material written by Ed](https://github.com/leanprover-community/mathlib4/blob/tutorial/docs/metaprogramming/02_metavariables.md)

## Contributing

The markdown files are generated automatically via [lean2md](https://github.com/arthurpaulino/lean2md).
Thus, if you're going to write or fix content for the book, please do so in the original Lean files inside the [lean](lean) directory.

**Important**: since `lean2md` is so simple, please avoid using comment sections
in Lean code blocks with `/- ... -/`. If you want to insert commentaries, do so
with double dashes `--`.

To open the PR, select `dev` as the target branch.

### Building the markdown files

This is not required, but if you want to build the markdown files, you can do so by running `lake run build`.
It requires having Python installed, as well as the `lean2md` package.

Or, if you have [viper](https://github.com/arthurpaulino/viper) installed and a linked environment that has `lean2md`, you can call `lake run viper_build`.
