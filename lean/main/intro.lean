/-
# Introduction

## What's the goal of this book?

This book aims to build up enough knowledge about metaprogramming in Lean 4 so
you can be comfortable enough to:

* Start building your own meta helpers
* Read and discuss metaprogramming API's like the ones in Lean 4 core and
Mathlib4

We by no means intend to provide an exhaustive exploration/explanation of the
entire Lean 4 metaprogramming API. We also don't cover the topic of monadic
programming in Lean 4. However, we hope that the examples provided will be
simple enough for the reader to follow and comprehend without a super deep
understanding of monadic programming.

## Book structure

The book is organized in a way to build up enough content for the chapters that
cover DSLs and tactics. Backtracking the pre-requisites for each chapter, the
dependency structure is as follows:

* "Tactics" builds on top of "Macros" and "Elaboration"
* "DSLs" builds on top of "Elaboration"
* "Macros" builds on top of "`Syntax`"
* "Elaboration" builds on top of "`Syntax`" and "`MetaM`"
* "`MetaM`" builds on top of "Expressions"

After the chapter on tactics, you find a cheat-sheet containing a wrap-up of key
concepts and functions. And after that, There are some chapters with extra
content, showing other applications of metaprogramming in Lean 4.

The rest of this chapter is a gentle introduction for what metaprogramming is,
offering some small examples to serve as appetizers for what the book shall
cover. 

## What does it mean to be in meta?

When we write code in most programming languages such as Python, C, Java or
Scala, we usually have to stick to a pre-defined syntax otherwise the compiler
or the interpreter won't be able to figure out what we're trying to say. In
Lean, that would be defining an inductive type, implementing a function, proving
a theorem etc. The compiler, then, has to parse the code, build an abstract
syntax tree and elaborate its syntax nodes into terms that can be processed by
the language kernel. We say that such activities performed by the compiler are
done in the __meta-level__, which will be studied throughout the book. And we
also say that the common usage of the language syntax is done in the
__object-level__.

In most systems, the meta-level activities are done in a different language to
the one that we use to write code. In Isabelle, the meta-level language is ML
and Scala. In Coq, it's OCaml. In Agda it's Haskell. In Lean 4, the meta code is
mostly written in Lean itself, with a few components written in C++.

One cool thing about Lean, though, is that it allows us to define custom syntax
nodes and to implement our own meta-level routines to elaborate those in the
very same development environment that we use to perform object-level
activities. So for example, one can write their own notation to instantiate a
term of a certain type and use it right away, on the same file! This concept is
generally called
[__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). We can
say that, in Lean, the meta-level is _reflected_ to the object-level.

Since the objects defined in the meta-level are not the ones we're most
interested in proving theorems about, it can sometimes be overly tedious to
prove that they are type correct. For example, we don't care about proving that
a recursive function to traverse an expression is well founded. Thus, we can
use the `partial` keyword if we're convinced that our function terminates. In
the worst case scenario, our function gets stuck in a loop but the kernel is
not reached/affected.

Let's see some example use cases of metaprogramming in Lean.

## Metaprogramming examples

The following examples are meant for mere illustration. Don't worry if you don't
understand the details for now.

### Building a command

Suppose we want to build a helper command `#assertType` which tells whether a
given term is of a certain type. The usage will be:

`#assertType <term> : <type>`

Let's see the code:
-/

import Lean

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM `assertTypeCmd
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch | _ => throwError "failure"

#assertType 5  : Nat -- success
#assertType [] : Nat -- failure

/-! We started by using `elab` to define a `command` syntax, which, when parsed
by the compiler, will trigger the incoming computation.

At this point, the code should be running in the `CommandElabM` monad. We then
use `liftTermElabM` to access the `TermElabM` monad, which allows us to use
`elabType` and `elabTermEnsuringType` in order to build expressions out of the
syntax nodes `typeStx` and `termStx`.

First we elaborate the expected type `tp : Expr` and then we use it to elaborate
the term expression, which should have the type `tp` otherwise an error will be
thrown. The term expression itself doesn't matter to us here, as we're calling
`elabTermEnsuringType` as a sanity check.

We also add `synthesizeSyntheticMVarsNoPostponing`, which forces Lean to
elaborate metavariables right away. Without that line, `#assertType 5  : ?_`
would result in `success`.

If no error is thrown until now then the elaboration succeeded and we can use
`logInfo` to output "success". If, instead, some error is caught, then we use
`throwError` with the appropriate message.

### Building a DSL and a syntax for it

Let's parse a classic grammar, the grammar of arithmetic expressions with
addition, multiplication, naturals, and variables.  We'll define an AST
(Abstract Syntax Tree) to encode the data of our expressions, and use operators
`+` and `*` to denote building an arithmetic AST. Here's the AST that we will be
parsing:
-/

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | nat : Nat → Arith           -- constant
  | var : String → Arith        -- variable

/-! Now we declare a syntax category to describe the grammar that we will be
parsing. Notice that we control the precedence of `+` and `*` by giving a lower
precedence weight to the `+` syntax than to the `*` syntax indicating that
multiplication binds tighter than addition (the higher the number, the tighter
the binding). This allows us to declare _precedence_ when defining new syntax.
-/

declare_syntax_cat arith
syntax num                        : arith -- nat for Arith.nat
syntax str                        : arith -- strings for Arith.var
syntax:50 arith:50 " + " arith:51 : arith -- Arith.add
syntax:60 arith:60 " * " arith:61 : arith -- Arith.mul
syntax " ( " arith " ) "          : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

-- Our macro rules perform the "obvious" translation:
macro_rules
  | `(⟪ $s:str ⟫)              => `(Arith.var $s)
  | `(⟪ $num:num ⟫)            => `(Arith.nat $num)
  | `(⟪ $x:arith + $y:arith ⟫) => `(Arith.add ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ $x:arith * $y:arith ⟫) => `(Arith.mul ⟪ $x ⟫ ⟪ $y ⟫)
  | `(⟪ ( $x ) ⟫)              => `( ⟪ $x ⟫ )

#check ⟪ "x" * "y" ⟫
-- Arith.mul (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + "y" ⟫
-- Arith.add (Arith.var "x") (Arith.var "y") : Arith

#check ⟪ "x" + 20 ⟫
-- Arith.add (Arith.var "x") (Arith.nat 20) : Arith

#check ⟪ "x" + "y" * "z" ⟫ -- precedence
-- Arith.add (Arith.var "x") (Arith.mul (Arith.var "y") (Arith.var "z")) : Arith

#check ⟪ "x" * "y" + "z" ⟫ -- precedence
-- Arith.add (Arith.mul (Arith.var "x") (Arith.var "y")) (Arith.var "z") : Arith

#check ⟪ ("x" + "y") * "z" ⟫ -- brackets
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

/-!
### Writing our own tactic

Let's create a tactic that adds a new hypothesis to the context with a given
name and postpones the need for its proof to the very end. It's similar to
the `suffices` tactic from Lean 3, except that we want to make sure that the new
goal goes to the bottom of the goal list.

It's going to be called `suppose` and is used like this:

`suppose <name> : <type>`

So let's see the code:
-/

open Lean Meta Elab Tactic Term in
elab "suppose " n:ident " : " t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  withMVarContext mvarId do
    let t ← elabType t
    let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← intro1P $ ← assert mvarId n t p
    replaceMainGoal [p.mvarId!, mvarIdNew]
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]; rfl     -- closes the initial main goal
  rw [Nat.zero_add]; rfl -- proves `add_comm`

/-! We start by storing the main goal in `mvarId` and using it as a parameter of
`withMVarContext` to make sure that our elaborations will work with types that
depend on other variables in the context.

This time we're using `mkFreshExprMVar` to create a metavariable expression for
the proof of `t`, which we can introduce to the context using `intro1P` and
`assert`.

To require the proof of the new hypothesis as a goal, we call `replaceMainGoal`
passing a list with `p.mvarId!` in the head. And then we can use the
`rotate_left` tactic to move the recently added top goal to the bottom.

## Printing Messages

In the `#assertType` example, we used `logInfo` to make our command print
something. If, instead, we just want to perform a quick debug, we can use
`dbg_trace`.

They behave a bit differently though, as we can see below:
-/

elab "traces" : tactic => do
  let array := List.replicate 2 (List.range 3)
  Lean.logInfo m!"logInfo: {array}"
  dbg_trace f!"dbg_trace: {array}"

example : True := by -- `example` is underlined in blue, outputting:
                     -- dbg_trace: [[0, 1, 2], [0, 1, 2]]
  traces -- now `traces` is underlined in blue, outputting
         -- logInfo: [[0, 1, 2], [0, 1, 2]]
  trivial
