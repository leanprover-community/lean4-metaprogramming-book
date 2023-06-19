/-
# Overview

In this chapter, we will provide an overview of the primary steps involved in the Lean compilation process, including parsing, elaboration, and evaluation. As alluded to in the introduction, metaprogramming in Lean involves plunging into the heart of this process. We will explore the fundamental objects involved, `Expr` and `Syntax`, learn what they signify, and discover how one can be turned into another (and back!).

In the next chapters, you will learn the particulars. As you read on, you might want to return to this chapter occasionally to remind yourself of how it all fits together.

## Connection to compilers

Metaprogramming in Lean is deeply connected to the compilation steps - parsing, syntactic analysis, transformation, and code generation.

> Lean 4 is a reimplementation of the Lean theorem prover in Lean itself. The new compiler produces C code, and users can now implement efficient proof automation in Lean, compile it into efficient C code, and load it as a plugin. In Lean 4, users can access all internal data structures used to implement Lean by merely importing the Lean package.
>
> Leonardo de Moura, Sebastian Ullrich ([The Lean 4 Theorem Prover and Programming Language](https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf))

Lean compilation process can be summed up in the following diagram:

<p align="center">
<img width="700px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/78867009-2624-46a3-a1f4-f488fd25d494"/>
</p>

First we will have Lean code as a string. Then `Syntax` object. Then `Expr` object. Then we can execute it.  

So, the compiler sees a string of Lean code, say `"let a := 2"`, and the following process unfolds:

1. **apply a relevant syntax rule** (`"let a := 2"` ➤ `Syntax`)  

    During the parsing step, Lean tries to match a string of Lean code to one of the declared **syntax rules** in order to turn that string into the `Syntax` object. **Syntax rules** are basically glorified regular expressions - when you write a Lean string that matches a certain **syntax rule**'s regex, that rule will be used to handle subsequent steps.

2. **apply all macros in a loop** (`Syntax` ➤ `Syntax`)  

    During the elaboration step, each **macro** simply turns the existing `Syntax` object into some new `Syntax` object. Then, the new `Syntax` is processed in a similar way (steps 1 and 2), until there are no more **macros** to apply.

3. **apply a single elab** (`Syntax` ➤ `Expr`)  

    Finally, it's time to infuse your syntax with meaning - Lean finds an **elab** that's matched to the appropriate **syntax rule** by the `:name` argument (**syntax rules**, **macros** and **elabs** all have this argument, and they must match). The newfound **elab** returns a particular `Expr` object.
    This completes the elaboration step.

Expression (`Expr`) is then converted to the executable code during the evaluation step - we don't have to specify that in any way, Lean compiler will handle that for us.

## Elaboration and delaboration

Elaboration is a overloaded term in Lean, for example you can meet the following usage of the word "elaboration", which defines elaboration as *"taking a partially-specified expression and inferring what is left implicit"*:


> When you enter an expression like `λ x y z, f (x + y) z` for Lean to process, you are leaving information implicit. For example, the types of `x`, `y`, and `z` have to be inferred from the context, the notation `+` may be overloaded, and there may be implicit arguments to `f` that need to be filled in as well.
>
> The process of *taking a partially-specified expression and inferring what is left implicit* is known as **elaboration**. Lean's **elaboration** algorithm is powerful, but at the same time, subtle and complex. Working in a system of dependent type theory requires knowing what sorts of information the **elaborator** can reliably infer, as well as knowing how to respond to error messages that are raised when the elaborator fails. To that end, it is helpful to have a general idea of how Lean's **elaborator** works.
>
> When Lean is parsing an expression, it first enters a preprocessing phase. First, Lean inserts "holes" for implicit arguments. If term t has type `Π {x : A}, P x`, then t is replaced by `@t _` everywhere. Then, the holes — either the ones inserted in the previous step or the ones explicitly written by the user — in a term are instantiated by metavariables `?M1`, `?M2`, `?M3`, .... Each overloaded notation is associated with a list of choices, that is, the possible interpretations. Similarly, Lean tries to detect the points where a coercion may need to be inserted in an application `s t`, to make the inferred type of t match the argument type of `s`. These become choice points too. If one possible outcome of the elaboration procedure is that no coercion is needed, then one of the choices on the list is the identity.  
>
> ([Theorem Proving in Lean 2](http://leanprover.github.io/tutorial/08_Building_Theories_and_Proofs.html))

We, on the other hand, just defined elaboration as the process of turning `Syntax` objects into `Expr` objects.

These definitions are not mutually exclusive - elaboration is, indeed, the transformation of `Syntax` into `Expr`s - it's just so that for this transformation to happen we need a lot of trickery - we need to infer implicit arguments, instantiate metavariables, perform unification, resolve identifiers, etc. etc. - and these actions can be referred to as "elaboration" on their own; similarly to how "checking if you turned off the lights in your apartment" (metavariable instantiation) can be referred to as "going to school" (elaboration).

There also exists a process opposite to elaboration in Lean - it's called, appropriately enough, delaboration. During delaboration, `Expr` is turned into the `Syntax` object; and then the formatter turns it into a `Format` object, which can be displayed in Lean's infoview. Every time you log something to the screen, or see some output upon hovering over `#check`, it's the work of the delaborator.

Throughout this book you will see references to the elaborator; and in the "Extra: Pretty Printing" chapter you can read on delaborators.

## 3 essential commands and their syntax sugars

Now, when you're reading Lean source code, you will see 11(+?) commands specifying the **parsing**/**elaboration**/**evaluation** process:

<p align="center">
<img width="500px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/9b83f06c-49c4-4d93-9d42-72e0499ae6c8"/>
</p>

In the image above, you see `notation`, `prefix`, `infix`, and `postfix` - all of these are combinations of `syntax` and `@[macro xxx] def ourMacro`, just like `macro`. These commands differ from `macro` in that you can only define syntax of particular form with them.

All of these commands are used in Lean and Mathlib source code extensively, so it's well worth memorizing them. Most of them are syntax sugars, however, and you can understand their behaviour by studying the behaviour of the following 3 low-level commands: `syntax` (a **syntax rule**), `@[macro xxx] def ourMacro` (a **macro**), and `@[command_elab xxx] def ourElab` (an **elab**).

To give a more concrete example, imagine we're implementing a `#help` command, that can also be written as `#h`. Then we can write our **syntax rule**, **macro**, and **elab** as follows:

<p align="center">
<img width="900px" src="https://github.com/lakesare/lean4-metaprogramming-book/assets/7578559/adc1284f-3c0a-441d-91b8-7d87b6035688"/>
</p>

This image is not supposed to be read row by row - it's perfectly fine to use `macro_rules` together with `elab`. Suppose, however, that we used the 3 low-level commands to specify our `#help` command (the first row). After we've done this, we can write `#help "#explode"` or `#h "#explode"`, both of which will output a rather parsimonious documentation for the `#explode` command (by the way - `#explode` is a real command from Mathlib 4, as is `#help`) - *"Displays proof in a Fitch table"*.

If we write `#h "#explode"`, the **syntax rule** with the name `:shortcut_h` will match it (remember the regex analogy). After that, Lean will find the **macro** with the same name, which will turn `#h "#explode"` into `#help "#explode"`. After that, the **syntax rule** with the name `:default_h` will match it. After that, Lean, having found no **macros** with the name `:default_h`, will find an **elab** with the name `:default_h` - and we'll see *"Displays proof in a Fitch table"* logged in VSCode's infoview.

If we used `macro_rules` or other syntax sugars, Lean would figure out the appropriate `name` attributes on its own.

If we were defining something other than a command, instead of `: command` we could write `: term`, or `: tactic`, or any other syntax category.  
The elab function can also be of different types - the `CommandElab` we used to implement `#help` - but also `TermElab` and `Tactic`:  

- `TermElab` stands for **Syntax → Option Expr → TermElabM Expr**, so the elab function is expected to return the **Expr** object.  
- `CommandElab` stands for **Syntax → CommandElabM Unit**, so it shouldn't return anything.  
- `Tactic` stands for **Syntax → TacticM Unit**, so it shouldn't return anything either.  

This corresponds to our intuitive understanding of terms, commands and tactics in Lean - terms return a particular value upon execution, commands modify the environment or print something out, and tactics modify the proof state.

## Order of execution: syntax rule, macro, elab

We have hinted at the flow of execution of these three essential commands here and there, however let's lay it out explicitly. The order of execution follows the following pseudocodey template: `syntax (macro; syntax)* elab`.

Consider the following example.

-/
import Lean
open Lean Elab Command

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

red -- finally, blue!

/-

The process is as follows:

- match appropriate `syntax` rule (happens to have `name := xxx`) ➤  
    apply `@[macro xxx]` ➤

- match appropriate `syntax` rule (happens to have `name := yyy`) ➤  
    apply `@[macro yyy]` ➤

- match appropriate `syntax` rule (happens to have `name := zzz`) ➤  
    can't find any macros with name `zzz` to apply,  
    so apply `@[command_elab zzz]`.  🎉.

The behaviour of syntax sugars (`elab`, `macro`, etc.) can be understood from these first principles.

## Manual conversions between `Syntax`/`Expr`/executable-code

Lean will execute the aforementioned **parsing**/**elaboration**/**evaluation** steps for you automatically if you use `syntax`, `macro` and `elab` commands, however, when you're writing your tactics, you will also frequently need to perform these transitions manually. You can use the following functions for that:

<p align="center">
<img width="650px" src="https://github.com/arthurpaulino/lean4-metaprogramming-book/assets/7578559/b403e650-dab4-4843-be8c-8fb812695a3a"/>
</p>

Note how all functions that let us turn `Syntax` into `Expr` start with "elab", short for "elaboration"; and all functions that let us turn `Expr` (or `Syntax`) into `actual code` start with "eval", short for "evaluation".

## Assigning meaning: macro VS elaboration?

In principle, you can do with a `macro` (almost?) anything you can do with the `elab` function. Just write what you would have in the body of your `elab` as a syntax within `macro`. However, the rule of thumb here is to only use `macro`s when the conversion is simple and truly feels elementary to the point of aliasing. As Henrik Böving puts it: "as soon as types or control flow is involved a macro is probably not reasonable anymore" ([Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/The.20line.20between.20term.20elaboration.20and.20macro/near/280951290)).  

So - use `macro`s for creating syntax sugars, notations, and shortcuts, and prefer `elab`s for writing out code with some programming logic, even if it's potentially implementable in a `macro`.

## Additional comments

Finally - some notes that should clarify a few things as you read the coming chapters.

### Printing Messages

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

/-
### Type correctness

Since the objects defined in the meta-level are not the ones we're most
interested in proving theorems about, it can sometimes be overly tedious to
prove that they are type correct. For example, we don't care about proving that
a recursive function to traverse an expression is well founded. Thus, we can
use the `partial` keyword if we're convinced that our function terminates. In
the worst case scenario, our function gets stuck in a loop, Lean server crashes
in VSCode, but the soundness of the underlying type theory implemented in kernel
isn't affected.
-/