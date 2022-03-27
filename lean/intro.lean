import Lean

/-!
# Introduction

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
our `Expr` recursion function is well founded. Thus, we can use the `partial`
keyword if we're convinced that our function terminates. In the worst case
scenario, our custom elaboration loops but the kernel is not reached/affected.

Let's see some exemple use cases of metaprogramming in Lean.

## Metaprogramming examples

The following examples are meant for mere illustration. Don't worry if you don't
understand the details for now.

### Building a command

Suppose we want to build a helper command `#assertType` which tells whether a
given term is of a certain type. The usage will be:

`#assertType <term> : <type>`
-/

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean.Elab Command Term in
  liftTermElabM `assertTypeCmd
    try
      let tp ← elabType typeStx
      let tm ← elabTermEnsuringType termStx tp
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
the term `tm : Expr`, which should have the type `tp` otherwise an error will be
thrown.

We also add `synthesizeSyntheticMVarsNoPostponing`, which forces Lean to
elaborate metavariables right away. Without that line, `#assertType 5  : ?_`
would result in `success`.

If no error is thrown until now then the elaboration succeeded and we can use
`logInfo` to output "success". If, instead, some error is caught, then we use
`throwError` with the appropriate message.

### Building a DSL and a syntax for it

Let's parse a classic grammar, the grammar of arithmetic expressions with
addition, multiplication, integers, and variables.  In the process, we'll learn
how to:

1. Convert identifiers such as `x` into strings within a macro.
2. Add the ability to "escape" the macro context from within the macro. This is useful to interpret identifiers with their _original_ meaning (predefined values)
   instead of their new meaning within a macro (treat as a symbol).

Let's begin with the simplest thing possible. We'll define an AST, and use operators `+` and `*` to denote
building an arithmetic AST.
Here's the AST that we will be parsing:
-/

inductive Arith : Type where
  | add : Arith → Arith → Arith -- e + f
  | mul : Arith → Arith → Arith -- e * f
  | int : Int → Arith -- constant
  | symbol : String → Arith -- variable

/-!
We declare a syntax category to describe the grammar that we will be parsing.
See that we control the precedence of `+` and `*` by writing `syntax:50` for addition and `syntax:60` for multiplication,
indicating that multiplication binds tighter than addition (higher the number, tighter the binding).
This allows us to declare _precedence_ when defining new syntax.
-/

declare_syntax_cat arith
syntax num : arith -- int for Arith.int
syntax str : arith -- strings for Arith.symbol
syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
syntax:70 arith:70 "*" arith:71 : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions

/-!
Further, if we look at `syntax:60  arith:60 "+" arith:61 : arith`, the
precedence declarations at `arith:60 "+" arith:61` conveys that the left
argument must have precedence at least `60` or greater, and the right argument
must have precedence at least`61` or greater.  Note that this forces left
associativity. To understand this, let's compare two hypothetical parses:

```
-- syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
-- a + b + c
(a:60 + b:61):60 + c
a + (b:60 + c:61):60
```

In the parse tree of `a + (b:60 + c:61):60`, we see that the right argument `(b + c)` is given the precedence `60`. However,
the rule for addition expects the right argument to have a precedence of **at least** 61, as witnessed by the `arith:61` at
the right-hand-side of `syntax:60 arith:60 "+" arith:61 : arith`. Thus, the rule `syntax:60  arith:60 "+" arith:61 : arith`
ensures that addition is left associative.

Since addition is declared arguments of precedence `60/61` and multiplication with `70/71`, this causes multiplication to bind
tighter than addition. Once again, let's compare two hypothetical parses:

```
-- syntax:60  arith:60 "+" arith:61 : arith -- Arith.add
-- syntax:70 arith:70 "*" arith:71 : arith -- Arith.mul
-- a * b + c
a * (b:60 + c:61):60
(a:70 * b:71):70 + c
```


While parsing `a * (b + c)`, `(b + c)` is assigned a precedence `60` by the addition rule. However, multiplication expects
the right argument to have precedence **at least** 71. Thus, this parse is invalid. In contrast, `(a * b) + c` assigns
a precedence of `70` to `(a * b)`. This is compatible with addition which expects the left argument to have precedence
**at least `60` ** (`70` is greater than `60`). Thus, the string `a * b + c` is parsed as `(a * b) + c`.
For more details, please look at the [Lean manual on syntax extensions](../syntax.md#notations-and-precedence).




To go from strings into `Arith`, We define a macro to
translate the syntax category `arith` into an `Arith` inductive value that
lives in `term`:
-/

-- auxiliary notation for translating `arith` into `term`
syntax "[Arith| " arith "]" : term


-- Our macro rules perform the "obvious" translation:
macro_rules
  | `([Arith| $s:strLit ]) => `(Arith.symbol $s)
  | `([Arith| $num:numLit ]) => `(Arith.int $num)
  | `([Arith| $x:arith + $y:arith ]) => `(Arith.add [Arith| $x] [Arith| $y])
  | `([Arith| $x:arith * $y:arith ]) => `(Arith.mul [Arith| $x] [Arith| $y])
  | `([Arith| ($x:arith) ]) => `([Arith| $x ])


-- some examples:

#check [Arith| "x" * "y"] -- Arith.mul (Arith.symbol "x") (Arith.symbol "y") : Arith
#check [Arith| "x" + "y"] --  Arith.add (Arith.symbol "x") (Arith.symbol "y") 

#check [Arith| "x" + 20] --  Arith.add (Arith.symbol "x") (Arith.int 20)



#check [Arith| "x" + "y" * "z" ] -- precedence
-- Arith.add (Arith.symbol "x") (Arith.mul (Arith.symbol "y") (Arith.symbol "z"))
-- 
#check [Arith| "x" * "y" + "z"] -- precedence
-- Arith.add (Arith.mul (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")


#check [Arith| ("x" + "y") * "z"] -- brackets
-- Arith.mul (Arith.add (Arith.symbol "x") (Arith.symbol "y")) (Arith.symbol "z")

/-!
### Writing our own tactic

Let's create a tactic that adds a new hypothesis to the context with a given
name and postpones the need for its proof to the very end. It's going to be
called `suppose` and is used like this:

`suppose <name> : <type>`
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
-/