import Lean

/-!
# Introduction

--todo: simple examples of
* tactic
* custom elaborator/DSL

## What does it mean to be in meta?

Part of the common tasks of a compiler is to parse a long string (e.g. the
source code in a file) into an abstract syntax tree and then elaborate the
syntax nodes into terms which can be processed by the language kernel.

But in order to construct these objects, we need to do activities that are
_outside_ the structure: expanding syntax nodes into others, deciding what type
theory to use, writing the code that manipulates trees of terms, applying
reductions to terms, checking that the inference rules are being applied
correctly and so on. Let's refer to these as __meta-level__ activities. And
let's refer to the activities performed within a fixed syntax and set of
elaboration rules as __object-level__ activities. Examples: defining an
inductive type, implementing a function, proving a theorem etc.

In most systems, the meta-level activities are done in a different language to
the one that we use to write code. In Isabelle, the meta-level language is ML
and Scala. In Coq, it's OCAML. In AGDA it's Haskell. In Lean 4, the meta code is
mostly written in Lean itself, with a few components written in C++.

One cool thing about Lean, though, is that it allows us to define custom syntax
nodes and to implement our own meta-level routines to elaborate those in the
very same development environment that we use to perform object-level
activities. So for example, one can write their own notation to instantiate a
term of a certain type and use it right away, on the same file! The general term
for this is
[__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). We can
say that the metal-level is _reflected_ to the object-level.

Since the objects defined in the meta-level are not the ones we're interested in
proving theorems about, it can sometimes be overly tedious to prove that they
are type correct. For example, we don't care about proving that our `Expr`
recursion function is well founded. But in Lean, you get an error if you try to
write a recursive function whose termination is not proven.

Lean relaxes these constraints with trust levels. You can add `unsafe` or
`partial` keywords to your declaration to flag that you don't care about
soundness for this function. Most of the time in Lean 4, you can write your
metaprogramming code without these keywords though, only use them as a last
resort.

Let's see some exemplary use cases of metaprogramming in Lean.

## Metaprogramming examples

The following examples are meant for mere illustration. Don't worry if you don't
understand the details for now.

### Building a command

Suppose we want to build a helper command `#assertType` which tells whether a
given term is of a certain type. The usage will be:

`#assertType <term> : <type>`

Let's also make it print out "success" or "failure" accordingly.
-/

open Lean.Elab.Command Lean.Elab.Term in
elab "#assertType " tmStx:term " : " tpStx:term : command =>
  liftTermElabM `test do
    try
      let tp ← elabTerm tpStx none
      let tm ← elabTermEnsuringType tmStx tp
      dbg_trace "success"
    catch | _ => dbg_trace "failure"

#assertType 5 : Nat  -- success
#assertType [] : Nat -- failure

/-!
### Writing our own tactic

### Building a DSL and a syntax for it
-/
