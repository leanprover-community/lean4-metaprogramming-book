/-!
# Monad Stacks
Before you read this: This chapter does not attempt to introduce the concept
of a monad in general, it assume this as a given and explains the monads
and constructs on top of them that are essential to Lean meta programming.
If you don't know what a monad is already you can read (TODO: Link to monad tutorial).

## Monad Transformers
Quite often in functional programming with monads one wants to have the power
of more than one monad available. Specifically in Lean meta programming it
is a very common pattern that we have some sort of read only input, an
execution context, available to us, as well as the ability to operate on
a mutable state. Both of these issues have monads that can solve them
separately already, namely the `Reader` monad for read only input and the
`StateM` monad for the mutable state. Now we can try to just "stack" them
ontop like this:`
-/
namespace Playground1
abbrev Context := Nat
abbrev State := String

abbrev MyM (α : Type) := Reader Context (StateM State α)

end Playground1
/-!
And this will indeed type check, however we have a very annoying issue,
if we attempt to synthesize a `Monad` instance for this via the `#synth` command:
-/
namespace Playground1

-- failed to synthesize
--  Monad MyM
#synth Monad MyM

def test1 : MyM Unit := pure () -- failure, pure requires a monad instance
def test2 : MyM Unit := do
  let res ← test1 -- failure, <- syntax requires a monad instance
  pure res -- same issue as with the pure above

end Playground1
/-!
We can fix this by manually declaring the instance though:
-/
namespace Playground1

instance : Monad MyM where
  pure x := fun ctx state => (x, state)
  bind x f := fun ctx state =>
    let (res, newState) := x ctx state
    f res ctx newState

end Playground1

/-!
Now while we can use bind, aka the `<-` Syntax and `pure` now we are still
missing convenience functions:
- `Reader` should give us `read` to get the context
- `StateM` should give us `get` and `set` to get and set the state
-/
namespace Playground1

def foo : MyM Unit := do
  let ctx ← read -- failure because read is not found, the bind syntax works
  let state ← get -- failure because get is not found, the bind syntax works
  set state -- failure because set is not found
  pure () -- pure also works thanks to the monad instance!

end Playground1
/-!
Now we could of course write all of these functions ourselves and keep repeating
ourselves whenever we do this sort of "combining monads" again but it would obviously
be much nicer if we could just have all of this done for us automatically.
This is where monad transformers come in. A monad transformer gives us a way
to combine the effects that certain monads give us (not all monad can be turned into
a transformer) in a nice way. For these monads specifically there is the `Reader`
transformer `ReaderT` and the `StateM` transformer `StateT`, let's see how they
perform:
-/
namespace Playground2
abbrev Context := Nat
abbrev State := String

-- `StateM` is defined as `StateM σ α = StateT σ Id α` so the following two are equivalent.
abbrev MyM  := ReaderT Context (StateT State Id)
abbrev MyM2  := ReaderT Context (StateM State)
-- This definition of `StateM` makes perfect sense since the `Id` monad has no effect,
-- so combining it with `StateT` will create a monad that has only the state effect.
-- Can you guess the definition of `Reader` based on `ReaderT`?

#synth Monad MyM -- monad instance!
#synth Monad MyM2 -- monad instance!

end Playground2
/-!
So that's the monad instance for free. The other thing that failed above,
was that we didn't have access to `read`, `get` and `set`, anymore, let's
see whether our monad transformers allow this:
-/
namespace Playground2

def testReader : MyM String := do
  let get ← read -- obtain our context
  pure s!"This is my context: {get}"

def testState (add : State) : MyM Unit := do
  let old ← get
  set s!"{old} + {add}"

def testStateChange : MyM String := do
  let _ ← testState "new stuff!"
  testState "more new stuff!"
  get

def MyM.run (context : Context) (state : State) (x : MyM α) : α :=
  Prod.fst <$> StateT.run (ReaderT.run x context) state

#eval MyM.run 12 "hello" testReader -- "This is my context: 12"
#eval MyM.run 12 "hello" testStateChange -- "hello + new stuff! + more new stuff!"

end Playground2
/-!
Nice! Everything just seems to work here, if you are interested in how
Lean does this internally you can check out the infrastructure around:
- `MonadReader`, `MonadReaderOf` for the `ReaderT` part
- `MonadState`, `MonadStateOf` for the `StateT` part

for most applications the idea that our `ReaderT` `StateT` monad transformers
just combine nicely out of the box is perfectly fine though.

### Lifting
The next interesting question one might come up with is, can we just combine
monad stacks nicely like this as well? What we are aiming for is that
assuming we have a monad stack `S` and another one of our monad stacks `MyM`,
that is built on top of `S`, we want to be able to execute computations inside of `S`
just as easily inside of `MyM` as well. Let's see if the built-in stacks
can do this already, as an example for `S` we will use the `IO` monad which is
a monad stack under the hood as well:
-/
namespace Playground3

abbrev Context := Nat
abbrev State := String

abbrev MyM  := ReaderT Context (StateT State IO)

def test : MyM Unit := do
  let old ← get
  let new := s!"Number {←read}, String: {old}"
  IO.println s!"Old was: {old}, New will be: {new}"
  set new

def MyM.run (context : Context) (state : State) (x : MyM α) : IO α :=
  Prod.fst <$> StateT.run (ReaderT.run x context) state

#eval MyM.run 12 "hello" test -- Old was: hello, New will be: Number 12, String: hello

end Playground3
/-!
This also just worked without any additional effort on our side! The infrastructure
responsible for this is `MonadLift` and `MonadLiftT` as well as some effort
in the implementation of `do` to figure out when to lift. However you can again
ignore this if you want, it just works out of the box most of the time.
-/

/-!
## Error monads
Next up we'll take a look at 2 monads you have most likely not heard of yet,
both of which will show up in meta programming.

First is `EStateM`, as it's name suggests it is very similar to `StateM` but
with the fundamental difference that it can throw some sort of `E`rror,
as such it is parameterized by 3 types: `EStateM Error State Value`.
It is one of the monads that implement the `MonadExcept`/`MonadExceptOf`
machinery which allows us to introduce a concept of exceptions into our
monad stacks:
-/
namespace Playground4

abbrev Context := Nat
abbrev Error := String
abbrev State := Nat

abbrev MyM := ReaderT Nat (EStateM Error State)

def alarm (x : String) : MyM Unit := do
  throw s!"Alarm!: {x}"

def main : MyM String := do
  alarm "hi"
  pure "test"

def MyM.run (context : Context) (state : State) (x : MyM α) : Sum α Error :=
  let res := EStateM.run (ReaderT.run x context) state
  match res with
  | .ok v _ => Sum.inl v
  | .error e _ => Sum.inr e

#eval MyM.run 12 13 main -- Sum.inr "Alarm!: hi"

end Playground4
/-!
What happened here is that `alarm` threw an exception and because we didn't
have any mechanism in place to catch it, the rest of our program didn't get
executed and the error got propagated up to us. Luckily Lean has some
nice built-in syntax to catch exceptions (if we want to do so):
-/
namespace Playground4

def main2 : MyM String := do
  try
    alarm "hi"
    pure "Success"
  catch err =>
    pure s!"Got an error: {err}"

#eval MyM.run 12 13 main2 -- Sum.inl "Got an error: Alarm!: hi"

end Playground4
/-!
There exists another monad that implements `MonadExcept`, its the one underlying `IO`, `EIO`.
`EIO` is basically `IO` but parameterized with an exception type.
`IO` sets this to the `IO.Error`, a type based on UNIX errno. Unsurprisingly
`EIO` (and thus `IO`) have the capability to throw exceptions.

Note: `EIO` is in fact based on `EStateM`, this is however not a tutorial on the inner
workings of `IO` so we will leave it at that.

### `StateRefT`
`StateT` is implemented as a function that forwards the state
from one monadic computation to the next like this: `State -> (Value, State)`.
Especially when updating the state lots of times this does of course become
rather inefficient so there is an alternative to it, `StateRefT`. Thanks to
`MonadState` the `StateRefT` transformer behaves basically identical to the
user. Internally it works with an `ST.Ref` which is in essence a truly
mutable memory location and thus much more efficient than ordinary `StateT`,
hence most of the meta programming monad stacks are implemented with it instead
of `StateT`. There is only a single issue with this, Lean is a pure programming
language so we can't just have mutable memory locations like that, this is why
`StateRefT` expects another monad stack that can provide this capability.
Right now these are:
- The `IO` family and stacks built on top of them, that is `IO`, `EIO` and `BaseIO`
- `EST` and stacks built on top of it, `EST` is a (not reducible) alias to `EStateM`
  (TODO: Figure out why this distinction is made)

For our example we will simply use `IO`.
-/
namespace Playground5

abbrev Context := Nat
abbrev State := String

abbrev MyM  := ReaderT Context (StateRefT State IO)

def test : MyM Unit := do
  let old ← get
  let new := s!"Number {←read}, String: {old}"
  IO.println s!"Old was: {old}, New will be: {new}"
  set new

def MyM.run (context : Context) (state : State) (x : MyM α) : IO α :=
  -- We use StateRefT' because StateRefT is actually a macro, figuring out the
  -- details on how to provide the mutable memory location based on the stack we are building on.
  Prod.fst <$> StateRefT'.run (ReaderT.run x context) state

#eval MyM.run 12 "hello" test -- Old was: hello, New will be: Number 12, String: hello

end Playground5

/-!
## More `Monad` type class extensions
Last but not least lets take a look at a few more, general, `Monad` extensions
that might be useful along the way.
### `MonadWithReader`
Provides a function `withReader : (ρ → ρ) → m α → m α` where `ρ` is the context
stored inside of a `Reader`. The idea is, that you pass it a function
that will be applied to your context and the resulting context will be passed on to
the second argument as its context, returning the result of that computation.
This allows you to temporarily change the context in some sub section of your
program before continuing with the original one. In order to make this accessible
in monad stacks as well there exists an equivalent machinery to `MonadReader`/`MonadReaderOf`,
named `MonadWithReaderOf`.
### `MonadFinally`
`MonadFinally` provides a function `tryFinally' : m α → (Option α → m β) → m (α × β)`
that works as follows: `tryFinally' x f` runs `x` and then the "finally" computation `f`.
When `x` succeeds with `a : α`, `f (some a)` is returned. If `x` fails for `m`'s definition
of failure, `f none` is returned. Hence `tryFinally'` can be thought of as performing the same
role as a finally block in an imperative programming language. (TODO: This is a docstring,
link to rendered documentation instead). Like above `MonadFinally` is implemented
so that it is accessible throughout monad stacks that are based on a monad which implements
this behaviour.
### `MonadBackTrack`
TODO: The doc string does explain what it does: Similar to MonadState,
but it retrieves/restores only the "backtrackable" part of the state.

However this is a little abstract and probably requires an example, the issue
with this is that all instances of `MonadBackTrack` are inside the meta stack
so I'm not quite sure how to do one.
### `MonadControl`
Is explained in an excellent doc string [here](https://github.com/leanprover/lean4/blob/575b1187c500af22bfc4c49c8aa58371d91843fa/src/Init/Control/Basic.lean#L69-L178)
### `MonadFunctor`
TODO: Again the doc string explains it: A functor in the category of monads.
Can be used to lift monad-transforming functions. Based on pipes' MFunctor,
but not restricted to monad transformers. Alternatively, an implementation
of MonadTransFunctor.

This might however be rather confusing to most people (including me) so
we should probably try to come up with some nice examples as well.
-/


/-!
# Monads used in Lean 4

Here is a list of monads that are used in Lean 4 that you might run into. Some have already been discussed above.
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
To summarise: it's essentially a placeholder for the current state of everything outside your app.
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
needed to expand macros hygienically. You can learn more about macros in [[main/macros]] and [The Lean manual](https://leanprover.github.io/lean4/doc/macro_overview.html).

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