```lean
import Lean
open Lean PrettyPrinter Delaborator SubExpr
```

# Pretty Printing
The pretty printer is what Lean uses to present terms that have been
elaborated to the user. This is done by converting the `Expr`s back into
`Syntax` and then even higher level pretty printing datastructures, this means
Lean does not actually recall the `Syntax` it used to create some `Expr`
there has to be code that tells it how to do that.
In the big picture, the pretty printer consists of three parts run in the
order they are listed in:
- the [delaborator](https://github.com/leanprover/lean4/tree/master/src/Lean/PrettyPrinter/Delaborator)
  this will be our main interest since we can easily extend it with our own code.
  Its job is to turn `Expr` back into `Syntax`.
- the [parenthesizer](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Parenthesizer.lean)
  responsible for adding parenthesis into the `Syntax` tree, where it thinks they would be useful
- the [formatter](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Formatter.lean)
  responsible for turning the parenthesized `Syntax` tree into a `Format` object that contains
  more pretty printing information like explicit whitespaces

## Delaboration
As its name suggests the delaborator is in a sense the opposite of the
elaborator. The job of the elaborator is to take an `Expr` produced by
the elaborator and turn it back into a `Syntax` which if elaborated
should produce an `Expr` that behaves equally to the input one.

Delaborators have the type `Lean.PrettyPrinter.Delaborator.Delab` which
is an alias for `DelabM Syntax` where `DelabM` is the delaboration monad,
all of this machinery is defined [here](https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Basic.lean).
`DelabM` provides us with quite a lot of options you can look up in the documentation
(TODO: Docs link), we will merely highlight the most relevant parts here:
- It has a `MonadQuotation` instance which allows us to declare `Syntax` objects
  using the familiar quotation syntax. 
- It can run `MetaM` code
- It has a `MonadExcept` instance for throwing errors.
- It can interact with `pp` options using functions like `whenPPOption`
- You can obtain the current subexpression using `SubExpr.getExpr`, there is
  also an entire API defined around this concept in the `SubExpr` module.

### Making our own
Like so many things in metaprogramming the elaborator is based on an attribute,
in this case the `delab` one. `delab` expects a `Name` as an argument,
this name has to start with the name of an `Expr` constructor, most commonly
`const` or `app`. This constructor name is then followed by the name of the
constant we want to delaborate, for example if we want to delaborate a function
`foo` in a special way we would use `app.foo`, let's see this in action:

```lean
def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)

#check foo -- 1 : Nat → Nat
#check foo 13 -- 1 : Nat, full applications are also pretty printed this way
```

This is obviously not a good delaborator since reelaborating this `Syntax`
will not yield the same `Expr`. Like with many other metaprogramming
attributes we can also overload delaborators:

```lean
@[delab app.foo]
def delabfoo2 : Delab := do
  `(2)

#check foo -- 2 : Nat → Nat
```

The mechanism for figuring out which one to use is the same as well, the
delaborators are tried in order, the ones last registered first until one
does not throw an error, indicating that it "feels unresponsible for the `Expr`".
In the case of delaborators this is done using `failure`

```lean
@[delab app.foo]
def delabfoo3 : Delab := do
  failure
  `(3)

#check foo -- 2 : Nat → Nat, still 2 since 3 failed
```

In order to write a proper delaborator for `foo` we will have to use some
slightly more advanced machinery though:

```lean
@[delab app.foo]
def delabfooFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `foo 1 -- only delab full applications this way
  let fn := mkIdent `fooSpecial
  let arg ← withAppArg delab
  `($fn $arg)

#check foo 42 -- fooSpecial 42 : Nat
#check foo -- 2 : Nat → Nat, still 2 since 3 failed
```

Can you extend `delabFooFinal` to also account for non full applications?

## Unexpanders
While delaborators are obviously quite powerful it is quite often not necessary
to use them, if you look in the Lean compiler for `@[delab` or rather `@[builtinDelab`
(a special version of the delab attribute for compiler use, we don't care about it),
you will see there are quite few occurences of it. This is because the majority
of pretty printing is in fact done by so called unexpanders. Unlike delaborators
they are of type `Lean.PrettyPrinter.Unexpander` which in turn is an alias for
`Syntax → Lean.PrettyPrinter.UnexpandM Syntax`. As you can see they are
`Syntax` to `Syntax` translations, quite similar to macros, except that they
are supposed to be the inverse of macros. The `UnexpandM` monad is quite a lot
weaker than `DelabM` but it still has:
- `MonadQuotation` for syntax quotations
- The ability to throw errors, although not very informative ones: `throw ()`
  is the only valid one

Unexpanders are always specific to applications of one constant, they are registered
using the `appUnexpand` attribute, followed by the name of said constant. The unexpander
is passed the entire application of the constant after the `Expr` has been delaborated,
without implicit arguments, let's see this in action:

```lean
def myid {α : Type} (x : α) := x

@[appUnexpander myid]
def unexpMyId : Unexpander
  -- hygiene disabled so we can actually return `id` without macro scopes etc.
  | `(myid $arg) => set_option hygiene false in `(id $arg)
  | `(myid) => pure $ mkIdent `id
  | _ => throw ()

#check myid 12 -- id 12 : Nat
#check myid -- id : ?m.3870 → ?m.3870
```

For a few nice examples of unexpanders you can take a look at
[NotationExtra](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean)

### Mini project
As per usual we will tackle a little mini project at the end of the chapter,
this time building our own unexpander for mini programming language.
Note that many ways to define syntax already have generation of the required
pretty printer code built-in, e.g. `infix`, and `notation` (however not `macro_rules`).
So for easy syntax you will never have to do this yourself.

```lean
declare_syntax_cat lang
syntax num : lang
syntax ident : lang
syntax "let " ident " := " lang " in " lang: lang
syntax "[Lang| " lang "]" : term

inductive LangExpr
  | numConst : Nat → LangExpr
  | ident : String → LangExpr
  | letE : String → LangExpr → LangExpr → LangExpr

macro_rules
  | `([Lang| $x:num ]) => `(LangExpr.numConst $x)
  | `([Lang| $x:ident]) => `(LangExpr.ident $(Lean.quote (toString x.getId)))
  | `([Lang| let $x:ident := $v:lang in $b:lang]) => `(LangExpr.letE $(Lean.quote (toString x.getId)) [Lang| $v] [Lang| $b])

-- LangExpr.letE "foo" (LangExpr.numConst 12)
--   (LangExpr.letE "bar" (LangExpr.ident "foo") (LangExpr.ident "foo")) : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]
```

As you can see the pretty printing output right now is rather ugly to look at,
we can do better with an unexpander:

```lean
@[appUnexpander LangExpr.numConst]
def unexpandNumConst : Unexpander
  | `(LangExpr.numConst $x:num) => `([Lang| $x])
  | _ => throw ()

@[appUnexpander LangExpr.ident]
def unexpandIdent : Unexpander
  | `(LangExpr.ident $x:str) =>
    if let some str := x.isStrLit? then
      let name := mkIdent $ Name.mkSimple str
      `([Lang| $name])
    else
      throw ()
  | _ => throw ()

@[appUnexpander LangExpr.letE]
def unexpandLet : Unexpander
  | `(LangExpr.letE $x:str [Lang| $v:lang] [Lang| $b:lang]) =>
    if let some str := x.isStrLit? then
      let name := mkIdent $ Name.mkSimple str
      `([Lang| let $name := $v in $b])
    else
      throw ()
  | _ => throw ()

-- [Lang| let foo := 12 in foo] : LangExpr
#check [Lang|
  let foo := 12 in foo
]

-- [Lang| let foo := 12 in let bar := foo in foo] : LangExpr
#check [Lang|
  let foo := 12 in
  let bar := foo in
  foo
]
```

That's much better! As always we encourage you to extend the language yourself
with things like parenthesized expressions, more data values, quotations for
`term` or whatever else comes to your mind.
