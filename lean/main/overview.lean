/-
# Overview

In this chapter, we will go through the fundamental concepts behind Lean metaprogramming, and how they interact. In the next chapters, you will learn the particulars. As you read on, you might want to return to this chapter occasionally to remind yourself of how it all fits together.

## Connection to compilers

Metaprogramming in Lean is deeply connected to the compilation steps - parsing, syntactic analysis, transformation, and code generation.

> Lean 4 is a reimplementation of the Lean theorem prover in Lean itself. The new compiler produces C code, and users can now implement efficient proof automation in Lean, compile it into efficient C code, and load it as a plugin. In Lean 4, users can access all internal data structures used to implement Lean by merely importing the Lean package.
>
> Leonardo de Moura, Sebastian Ullrich ([The Lean 4 Theorem Prover and Programming Language](https://pp.ipd.kit.edu/uploads/publikationen/demoura21lean4.pdf))


<img width="700px" src="https://71022.cdn.cke-cs.com/RructTCFEHceQFc13ldy/images/325233868b9e52982d5835dac90abfd1cc5a06be3eb0e41c.png/w_1592"/>  

First we will have Lean code as a string. Then `Syntax` object. Then `Expr` object. Then we can execute it.  
So, the compiler sees a string of Lean code, say `"let a := 2"`, and the following process unfolds:

1. **apply a relevant `syntax` rule** (`"let a := 2"` ➤ `Syntax`)  

    During the parsing step, Lean applies all declared `syntax` rules to turn a string of Lean code into the `Syntax` object. `syntax` rules are basically glorified regular expressions - when you write a Lean string that matches a certain `syntax` rule's regex, that rule will be used to handle subsequent steps.

2. **apply all `macro`s in a loop** (`Syntax` ➤ `Syntax`)  

    During the elaboration step, each `macro` simply turns the existing `Syntax` object into some new `Syntax` object. Then, the new `Syntax` is processed in a similar way (steps 1 and 2), until there are no more `macro`s to apply.

3. **apply a single `elab`** (`Syntax` ➤ `Expr`)  

    Finally, it's time to infuse your syntax with meaning - Lean finds an `elab` rule that's matched to the appropriate `syntax` rule by the name argument (both the `syntax` rule and `elab` rule have this argument, and they must match). The newfound `elab` returns a particular `Expr` object.
    This completes the elaboration step.

Expression (`Expr`) is then converted to the executable code during the evaluation step - we don't have to specify that in any way, Lean compiler will handle that for us.

## Elaboration and delaboration

Elaboration is a loaded term in Lean, for example you can meet the following usage of the word "elaboration", which defines elaboration as *"taking a partially-specified expression and inferring what is left implicit"*:


> When you enter an expression like `λ x y z, f (x + y) z` for Lean to process, you are leaving information implicit. For example, the types of `x`, `y`, and `z` have to be inferred from the context, the notation `+` may be overloaded, and there may be implicit arguments to `f` that need to be filled in as well.
>
> The process of *taking a partially-specified expression and inferring what is left implicit* is known as **elaboration**. Lean's **elaboration** algorithm is powerful, but at the same time, subtle and complex. Working in a system of dependent type theory requires knowing what sorts of information the **elaborator** can reliably infer, as well as knowing how to respond to error messages that are raised when the elaborator fails. To that end, it is helpful to have a general idea of how Lean's **elaborator** works.
>
> When Lean is parsing an expression, it first enters a preprocessing phase. First, Lean inserts "holes" for implicit arguments. If term t has type `Π {x : A}, P x`, then t is replaced by `@t _` everywhere. Then, the holes — either the ones inserted in the previous step or the ones explicitly written by the user — in a term are instantiated by metavariables `?M1`, `?M2`, `?M3`, .... Each overloaded notation is associated with a list of choices, that is, the possible interpretations. Similarly, Lean tries to detect the points where a coercion may need to be inserted in an application `s t`, to make the inferred type of t match the argument type of `s`. These become choice points too. If one possible outcome of the elaboration procedure is that no coercion is needed, then one of the choices on the list is the identity.  
>
> ([Theorem Proving in Lean 2](http://leanprover.github.io/tutorial/08_Building_Theories_and_Proofs.html))

These definitions are not mutually exclusive - elaboration is the transformation of `Syntax` into `Expr`s - it's just so that for this transformation to happen we need a lot of trickery - we need to infer implicit arguments, instantiate metavariables, perform unification, resolve identifiers, etc. etc. - and these actions can be referred to as "elaboration" on their own; similarly to how "checking if you turned off the lights in your apartment" (metavariable instantiation) can be referred to as "going to school" (elaboration).

There also exists a process opposite to elaboration in Lean - it's called, appropriately enough, delaboration. During delaboration, `Expr` is turned into the `Syntax` object; and then the formatter turns it into a `Format` object, which can be displayed in Lean's infoview. Every time you log something to the screen, or see some output upon hovering over `#check`, it's the work of delaborator.

Throughout this book you will see references to the elaborator; and in the "Pretty Printing" extra chapter you can read on delaborators.

## 3 essential functions and their syntax sugars

Now, when you're reading Lean source code, you will see 11(+?) commands specifying the **parsing**/**elaboration**/**evaluation** process.  Most of them are syntax sugar, and you only need **3 commands** to do metaprogramming in Lean:

- **syntax rule: `syntax (name := xxx) ... : command`**

    For example, `syntax (name := xxx) "#help" "option" (ident)? : command` is a syntax rule that will match (remember the regex analogy) all strings in the form of `"#help option hi.hello"` or just `"#help option"`.   
    Other widespread syntax categories are `tactic` and `term`, all of these are used in different physical places in your code.

- **macro: `@[macro xxx] def ourMacro : Macro := ...`**

    For example, ``@[macro xxx] def ourMacro : Macro := λ stx => match stx with | _ => `(tactic| pick_goal 2)``. Whenever your Lean code matches the syntax rule with the name `xxx`, this macro will be applied.  
    If the syntax rule was syntax `(name := xxx) "swap" : tactic`, this macro will syntactically turn `swap` into `pick_goal 2` - and the subsequent elaboration step will be handled by the `pick_goal 2` syntax rule.

- **elab: `@[command_elab xxx] def ourElab : CommandElab := ...`**

    For example, ``@[term_elab our_help] def ourElab : TermElab := λ stx tp => (Expr.app (Expr.const `Nat.add []))``.  
    Our `elab` function can be of different types - the **CommandElab** and **TermElab** that you saw already, and **Tactic**.  
    **TermElab** stands for **Syntax → Option Expr → TermElabM Expr**, so the elaboration function is expected to return the **Expr** object.  
    **CommandElab** stands for **Syntax → CommandElabM Unit**, so it shouldn't return anything.  
    **Tactic** stands for **Syntax → TacticM Unit**, so it shouldn't return anything either.  
    This corresponds to out intuitive understanding of terms, commands and tactics in Lean - terms return a particular value upon execution, commands modify the environment or print something out, and tactics modify the proof state.

These `syntax (name := xxx) ... : command`, `@[macro xxx] def ourMacro : Macro := ...` and `@[command_elab xxx] def ourElab : CommandElab := ...` are the 3 essential, low-level functions, and you can get away with them only. Lean standard library and Mathlib use many syntax sugars, however, so memorizing them is well worth the effort. I'm summing them up in the next diagram.

<img src="https://71022.cdn.cke-cs.com/RructTCFEHceQFc13ldy/images/118a91998ce7632aac13efad0cab55f476bf2a2b0c3706b1.png/w_2118"/>

In the image above, each row shows the commands that you have to use together (if you use one of them). For example, you cannot use `elab_rules` if you do not have the appropriate `syntax ~ : command` defined yet.

Let's consider **Syntax → Expr** commands:

- `syntax ~ : command` - low-level command we just discussed (I write `command` here for succinctness, but it can be `term`, `:tactic`, etc.).  

- `@[command_elab ~] def ~ : CommandElab` - low-level command we just discussed (I write `CommandElab` here for succinctness, but it can be `Tactic`, `TermElab`, etc.).  

- `elab_rules` - sugar for `@[command_elab ~] def ~ : CommandElab`.  

- `elab` - combination of `syntax ~ : command` and `@[command_elab ~] def ~ : CommandElab` 

Let's consider **Syntax → Expr** commands:

- `syntax ~ : command` - low-level command we just discussed.  

- `@[macro] def ~ : Macro` - low-level command we just discussed.  

- `macro_rules` - sugar for `@[macro] def ~ : Macro`.  

- `macro` - combination of `syntax ~ : command` and `@[macro] def ~ : Macro`.  

- `notation`, `prefix`, `infix`, `postfix` - combination of `syntax ~ : command` and `@[macro] def ~ : Macro` - they differ from `macro` in that you can only define rather simple syntax using them.

## Order of execution: syntax, macro, elab

We have hinted at the flow of execution of these three essential functions here and there, however let's lay it out explicitly. The order of execution follows the following pseudocodey template: `(syntax; macro)+ elab`.

Consider the following example.

-/
import Lean

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Lean.Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Lean.Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : Lean.Elab.Command.CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

red -- finally, blue!

/-

The process is as follows:

> match appropriate `syntax` rule (happens to have `name := xxx`) ➤  
> apply `@[macro xxx]` ➤
>
> match appropriate syntax rule (happens to have `name := yyy`) ➤  
> apply `@[macro yyy]` ➤
>
> match appropriate `syntax` rule (happens to have `name := zzz`) ➤  
> can't find any macros with name `zzz` to apply,  
> so apply `@[command_elab zzz]`.  🎉.

The behaviour of syntax sugars (`elab`, `macro`, etc.) can be understood from these first principles.

## Manual conversions between `Syntax`/`Expr`/executable-code

Lean will execute the afforementioned **parsing**/**elaboration**/**evaluation** steps for you automatically if you use `syntax`, `macro` and `elab` commands, however, when you're writing your tactics, you will also frequently need to perform these transitions manually. You can use the following functions for that:

<img width="650px" src="https://71022.cdn.cke-cs.com/RructTCFEHceQFc13ldy/images/11ed9f7c1e0b70a73922a06b24d94033b85028030fdd4670.png/w_1474"/>

Note how all functions that let us turn `Syntax` into `Expr` start with "elab", short for "elaboration"; and all functions that let us turn `Expr` (or `Syntax`) into `actual code` start with "eval", short for "evaluation".

## Assigning meaning: macro VS elaboration?

In principle, you can do with a `macro` (almost?) anything you can do with the `elab` function. Just write what you would have in the body of your `elab` as a syntax within `macro`. However, the rule of thumb here is to only use `macro`s when the conversion is simple and truly feels elementary to the point of aliasing. As Henrik Böving puts it: "as soon as types or control flow is involved a macro is probably not reasonable anymore" (Zulip thread)[https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/The.20line.20between.20term.20elaboration.20and.20macro/near/280951290]. So - use `macro`s for creating syntax sugars, notations, and shortcuts, and prefer `elab`s for writing out code with some programming logic, even if it's potentially implementable in a `macro`.

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
the worst case scenario, our function gets stuck in a loop but the kernel is
not reached/affected.
-/