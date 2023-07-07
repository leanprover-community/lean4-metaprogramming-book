```lean
import lean.extra.attrs.dummy
```

# Attributes

Attributes in Lean allows one to perform preprocessing on definitions. They are similar to Python's
decorators and Rust's proc-macros.

Unfortunately, it turns out that attributes must be defined in a separate module, so
we will bounce between this file and the files in the `attrs/` folder which
contain the implementations of the attributes. We'll see you at 
[`./attrs/dummy.lean`](./attrs/dummy.lean).

## Using the `dummy_attr`

We run the `dummy_attr`, and we see that we get access to the name
of the declaration (`foo`), the type of the declaration (`int`), and the
value of the declaration, which is the raw syntax tree.

```lean
@[dummy_attr]
def foo : Int := 42
-- src: foo | stx: (Attr.dummy_attr "dummy_attr") | kind: global
-- srcDecl:
--   name: foo
--   type: Int
--   value?: (some (OfNat.ofNat.{0} Int 42 (Int.instOfNatInt 42)))
```

Below is an example of a declaration that does not have any value.

```lean
@[dummy_attr]
class bar 
-- src: bar | stx: (Attr.dummy_attr "dummy_attr") | kind: global
-- srcDecl:
--   name: bar
--   type: Type
--   value?: none
```

## Modifying the `value` with the `around` attribute

We're going to write an attribute that will modify a given definition

## Tagging: `interesting` Definitions
