/-!
#  Errors

Error handling is done with the `Except ε α` datatype. An `Except` is either `ok : α` or `error : ε`.
Errors of type `ε` are added to monads with `EStateM ε` or `ExceptT ε`. Here are some common choices of `ε` that are used throughout Lean:

- `Exception` is either an
  - `error (ref : Syntax) (msg : MessageData)` is for errors that a user should try to correct, (eg a tactic is not applicable). The ref syntax is used by the language server to figure out where to draw the red squiggly. MessageData is the message, but with support for interactivity in the Infoview (so you can see the types of terms etc.)
  - `internal (id : InternalExceptionId) (extra : KVMap)` is used for when lean crashes.
- `IO.Error` is specialised for errors that can happen during IO operations (rather than lean-specific errors).
  There is an error type for all of the errors that you might get from the OS while doing syscalls.
  There is also a `userError (msg : String)` for when you want to bundle a user error.
- `Empty` is used when you don't want to throw errors.

There are also a load of monad classes which are used to talk about errors

- `MonadExcept ε M` means that you have `tryCatch : M α → (ε → M α) → M α` and `throw : ε → M α` available.
  This in turn is used to drive the `throw`/`try`/`catch` syntax.
- `MonadError M` means that you can throw and catch `Exceptions` and make the `Exceptions` properly where it is aware of the context of the error, so that you can draw red squigglies in the right place and render messages interactively.
  - `MonadExcept Exception M`: it can throw and catch `Exception`s.
  - `MonadRef M` is to do with managing syntax hygiene. It looks like `MonadReader Syntax M`, but slightly different.
  - `AddErrorMessageContext M`. Which means that you can take some `MessageData` and add context information to it. For example if you had a message which had to render an mvar, in order for the infoview to show this properly you would need to tell the message what metavariable context to use.

## Alternative

There is also a class `Alternative M`, this is `∀ α, OrElse (M α)` and a `failure : ∀ α, M α`.
Note that in general `ExceptT

## Syntax for error handling

There are a few different mechanisms you can use for throwing stuff.

- `throwError "..."` uses `MonadError` and throws an Exception in your monad. The "..." is a MessageData string comprehension so you can do `" ... {e} ..."` where `e : Expr` and it will correctly render that in an interactive way which is nice.
  `throwErrorAt ref "..."` is similar, but you can specify which piece of syntax the squigglie should appear at.
- `throw` uses `MonadExcept`, so it doesn't do all the fancy message stuff that `throwError` does. A variant is `throwThe ε e` where you just make the instance of the `MonadError ε M` that you want explicit; this is useful if you have multiple instances of `MonadError _ M` flying around.
- `try/catch` syntax can be much nicer than manually handling the error cases with match blocks:
  ```lean
  try
    x
  catch
    | p₁ => asdf
    | p₂ => qwerty
  ```
- This is not strictly error handling, but is good to know about: if you are in a `do` block, you can pattern match the let expressions and have a 'failover' case
  ```
  do
    let head :: tail ← getGoals | e
  ```
  the `e : M α` is run if the pattern matching on the lhs of the `let` assignment fails.
- `guard p` will test `p` and then throw an error


-/