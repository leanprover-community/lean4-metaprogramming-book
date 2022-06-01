
/-!
# Monads used in Lean 4

Here is a list of monads that are used in Lean 4 that you might run in to. Some have already been discussed above.
Monad stacks can be quite tall in Lean 4. For example if we were to write out the full defininition of `TacticM`:

```lean
TacticM :=
  EStateM Exception IO.RealWorld
  |> StateRefT Core.State
  |> ReaderT Core.Context
  |> StateRefT Meta.State
  |> ReaderT Meta.Context
  |> StateRefT Elab.Term.State
  |> ReaderT Elab.Term.Context
  |> StateRefT Elab.Tactic.State
  |> ReaderT Elab.Tactic.Context
```

## The IO monads

An IO monad is used to create computations that interact with the rest of the computer.
Things like: connecting to the internet, writing files etc.
Use an IO monad to say, "hey! this code can cause arbitrary OS-level side effects".
TODO: potentially there will be a whole chapter on the IO API, so we will just focus on the monad here.

In Lean 4 there are a family of IO monads: `IO`, `EIO ε`, `BaseIO`.
`EIO ε` is the main one, it is defined as `EStateM ε IO.RealWorld`: you can throw errors of type `ε` and it has a strange state object called `IO.Realworld`.

This state is a little strange.
There is a magic definition `IO.RealWorld : Type := Unit`, that represents the 'io state' of your application.
You should never actually use `IO.RealWorld`.
A description of how it works in Haskell is given [here](https://www.well-typed.com/blog/2014/06/understanding-the-realworld/).
To summarise: it's essentially a placeholder for for the current state of everything outside your app.
It seems to just be some bookkeeping for the compiler (TODO: check with authorities), since if you are passing this `() : IO.Realworld` object around,
the optimiser will never try to reorder operations and so on.
You should always use `EIO` and items defined in terms of `EIO`, because of course you can't reset the state of reality.

The difference between `IO`, `BaseIO` and `EIO ε` are the exceptions that are thrown. `BaseIO` has no exceptions and `IO := EIO IO.Error`.
`IO.Error` is specialised for errors that can happen when interfacing with the OS (rather than lean-specific errors which use `Exception`).
There is an error type for all of the errors that you might get from the OS while doing syscalls.
There is also a `userError (msg : String)` for when you want to pass a user error.

## `CoreM`

The best way to think about `CoreM` is that it tracks everything Lean-related that doesn't yet involve managing expressions.
It's a set of common context and state for the other metaprogramming monads.
You can use this to running attribute handlers (`AttrM := CoreM`), manipulating the environment and setting options.

It is defined as `ReaderT Core.Context $ StateRefT Core.State $ EIO Exception`.

The main things in the context are:
- The options that are set. I.e. storing the settings from `set_option trace.simplify.rewrite true` commands.
- The current namespace.
- Which namespaces are currently open. That is, things that have been opened with the `open` command.

The main things in the state are:
- The current `Environment`
- The name generator (responsible for making sure that unique names are created.)
- The trace state (where messages to the user are stored)

## `MetaM`

`CoreM` is `MetaM` with a local context and a metavariable state.
It is used for building expressions where you need to handle metavariables and local contexts.
You can learn more about it in [[main/metam]].

## `TermElabM`

The `TermElabM` tracks a lot of extra information that is needed to turn Lean syntax in to expressions: pending elaboration problems, pending tactics to be executed, etc.
This is used for writing term elaborators. You will encounter it when writing `elab` methods for custom syntax.

## `TacticM`

The tactic monad.
This is `TermElabM` with a list of goals. It is used to implement your own tactics.

## `CommandElabM`

This one sits outside the main monad stack.
It works similarly to a combined `TermElabM` and `CoreM`. It is used for elaborating commands.

## `MacroM`

A macro is a function `Syntax → MacroM Syntax`. The macro state and context contains information
needed to expand macros hygenically. You can learn more about macros in [[main/macros]] and [The Lean manual](https://leanprover.github.io/lean4/doc/macro_overview.html).

## `RequestM`

This is used to handle the requests in the Lean language server from vscode or emacs.

## `ImportM`

TODO

## Conversion table

Often when writing monads you will want to run monad `A` in monad `B`.
This is done with 'running' and 'lifting' monads.
Here is a table giving methods that can be used to lift or run monads from other monads.

| run ↓ in → | IO | `CoreM`  | `MetaM`  | `TermElabM` | `TacticM` | `CommandElabM` |
| ----------- | ---- | -------  | -------  | ----------- |  -------- |  -------------- |
| IO        |   .   | `liftM`  | `liftM`  | `liftM`     |   `liftM`        | `liftM`
| `CoreM`     |   `CoreM.toIO`, `CoreM.run`   |    .      | `liftM`  | `liftM`     |   `liftM`        | `liftCoreM`
| `MetaM`     | `MetaM.toIO`     | `MetaM.run`      |    .      | `liftM`     |   `liftM`        |
| `TermElabM` |      |          |    `TermElabM.run`      |      .       |     `liftM`      | `runTermElabM`, `liftTermElabM`
| `TacticM`   |      |          |    |    `Lean.Elab.Tactic.run`         |       .    |
| `CommandElabM` | `CommandElabM.run`  |          |          |             |          |        .        |


If you are writing your own definitions involving monads, rather than specifically
using a concrete monad like `MetaM`, consider using a variable monad `M` with monad typeclasses for the
bits that you need: eg `[MonadEnv M]` if you are using the environment or `[MonadControlT MetaM M]` if you want to use the metavariable context.
Doing this means that you have to worry less about lifting and running concrete monads.


-/