import Lean

/-!
# Introduction

--todo: simple examples of
* tactic
* custom elaborator/DSL

## What does it mean to be in meta?

When we write code in most programming languages such as Python, C, Java or
Scala, we usually have to stick to a pre-defined syntax otherwise the compiler
or the interpreter won't be able to figure out what we're trying to say. In
Lean, that would be defining an inductive type, implementing a function, proving
a theorem etc. The compiler, then, has to parse the code, build an abstract
syntax tree and elaborate its syntax nodes into terms that can be processed by
the language kernel. We say that such activities performed by the compiler are
done in the __meta-level__, and that the common usage of the syntax is done in
the __object-level__.

In most systems, the meta-level activities are done in a different language to
the one that we use to write code. In Isabelle, the meta-level language is ML
and Scala. In Coq, it's OCAML. In AGDA it's Haskell. In Lean 4, the meta code is
mostly written in Lean itself, with a few components written in C++.

One cool thing about Lean, though, is that it allows us to define custom syntax
nodes and to implement our own meta-level routines to elaborate those in the
very same development environment that we use to perform object-level
activities. So for example, one can write their own notation to instantiate a
term of a certain type and use it right away, on the same file! This concept is
generally called
[__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). We can
say that, in Lean, the metal-level is _reflected_ to the object-level.

Since the objects defined in the meta-level are not the ones we're most
interested in proving theorems about, it can sometimes be overly tedious to
prove that they are type correct. For example, we don't care about proving that
our `Expr` recursion function is well founded. But in Lean, you get an error if
you try to write a recursive function whose termination is not proven.

Lean relaxes these constraints with trust levels. You can add `unsafe` or
`partial` keywords to your declaration to flag that you don't care about
soundness for this function. Most of the time in Lean 4, you can write your
metaprogramming code without these keywords though, only use them as a last
resort.

Let's see some exemple use cases of metaprogramming in Lean.

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
elab "#assertType " termStx:term " : " typeStx:term : command =>
  liftTermElabM `assertTypeCmd
    try
      let tp ← elabTerm termStx none
      let tm ← elabTermEnsuringType typeStx tp
      dbg_trace "success"
    catch | _ => dbg_trace "failure"

#assertType 5 : Nat  -- success
#assertType [] : Nat -- failure

/-! We started by using `elab` to define a `command` syntax, which, when parsed
by the compiler, will trigger the incoming computation.

At this point, the code should be running in the `CommandElabM` monad. We then
use `liftTermElabM` to access the `TermElabM` monad, which allows us to use
`elabTerm` and `elabTermEnsuringType` in order to build expressions out of the
syntax nodes `termStx` and `typeStx`.

First we elaborate the expected type `tp : Expr` and then we use it to elaborate
the term `tm : Expr`, which should have the type `tp` otherwise an error will be
thrown.

If no error is thrown then the elaboration succeeded and we use `dbg_trace` to
output that message. If, instead, we catch some error, we just print `failure`.

### Writing our own tactic

### Building a DSL and a syntax for it
-/
