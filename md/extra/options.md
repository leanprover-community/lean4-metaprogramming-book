```lean
import Lean
open Lean
```

# Options
Options are a way to communicate some special configuration to both
your meta programs and the Lean compiler itself. Basically it's just
a [`KVMap`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/KVMap.lean)
which is a simple map from `Name` to a `Lean.DataValue`. Right now there
are 6 kinds of data values:
- `String`
- `Bool`
- `Name`
- `Nat`
- `Int`
- `Syntax`

Setting an option to tell the Lean compiler to do something different
with your program is quite simple with the `set_option` command:

```lean
#check 1 + 1 -- 1 + 1 : Nat

set_option pp.explicit true -- No custom syntax in pretty printing

#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

set_option pp.explicit false
```

You can furthermore limit an option value to just the next command or term:

```lean
set_option pp.explicit true in
#check 1 + 1 -- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) 1 1 : Nat

#check 1 + 1 -- 1 + 1 : Nat

#check set_option trace.Meta.synthInstance true in 1 + 1 -- the trace of the type class synthesis for `OfNat` and `HAdd`
```

If you want to know which options are available out of the Box right now
you can simply write out the `set_option` command and move your cursor
to where the name is written, it should give you a list of them as auto
completion suggestions. The most useful group of options when you are
debugging some meta thing is the `trace.` one.

## Options in meta programming
Now that we know how to set options, let's take a look at how a meta program
can get access to them. The most common way to do this is via the `MonadOptions`
type class, an extension to `Monad` that provides a function `getOptions : m Options`.
As of now, it is implemented by:
- `CoreM`
- `CommandElabM`
- `LevelElabM`
- all monads to which you can lift operations of one of the above (e.g. `MetaM` from `CoreM`)

Once we have an `Options` object, we can query the information via `Options.get`.
To show this, let's write a command that prints the value of `pp.explicit`.

```lean
elab "#getPPExplicit" : command => do
  let opts ← getOptions
  -- defValue = default value
  Elab.logInfo s!"pp.explicit : {opts.get pp.explicit.name pp.explicit.defValue}"

#getPPExplicit -- pp.explicit : false

set_option pp.explicit true in
#getPPExplicit -- pp.explicit : true
```

Note that the real implementation of getting `pp.explicit`, `Lean.getPPExplicit`,
uses whether `pp.all` is set as a default value instead.

## Making our own
Declaring our own option is quite easy as well. The Lean compiler provides
a macro `register_option` for this. Let's see it in action:

```lean
register_option book.myGreeting : String := {
  defValue := "Hello World"
  group := "pp"
  descr := "just a friendly greeting"
}
```

However, we cannot just use an option that we just declared in the same file
it was declared in because of initialization restrictions.
