```lean
import lean.extra.attrs.dummy
import lean.extra.attrs.tag
import lean.extra.attrs.parametric
import lean.extra.attrs.simp
```

# Attributes

Attributes in Lean allows one to perform preprocessing on definitions.
They are similar to Python's decorators and Rust's proc-macros.

Unfortunately, it turns out that attributes must be defined in a separate module, so
we will bounce between this file and the files in the `attrs/` folder which
contain the implementations of the attributes. We'll see you at 
[`./attrs/tag.lean`](./attrs/tag.lean).

## Tag attributes with `myTag`

see that we've created a tagging infrastructure based on Lean's `TagAttribute`s, which exists
explicitly to allow us to create 'simple' attributes that wish to keep track of
definitions that have been tagged with a given attribute, and nothing more.

```lean
@[myTag]
def tag1 : Int := 1

@[myTag]
def tag2 : Int := 2

@[myTag]
def tag3 : Int := 3
```

See that we can access all the declarations that have been tagged with @[myTag].
This simplified mechanism exists to allow us to easily tag definitions of interest.

```lean
-- decl: tag3 | find? OfNat.ofNat.{0} Int 3 (Int.instOfNatInt 3)
-- decl: tag1 | find? OfNat.ofNat.{0} Int 1 (Int.instOfNatInt 1)
-- decl: tag2 | find? OfNat.ofNat.{0} Int 2 (Int.instOfNatInt 2)
```

## Parametric attributes with `myParam`

A parametric attribute is like a tag attribute, while adding support for
parameters in the attribute. 

We shall add an attribute called `myParam`, which recieves two parameters,
a priority, denoted by a natural number, and an optional tag `important`.


We'll see you at [`./attrs/parametric.lean`](./attrs/dummy.lean).

```lean
@[myParam 10] def h1 (x : Nat) := 2*x + 1
@[myParam 20 important] def h2 (x : Nat) := 2*x + 1
```

## Using `simpAttr`

```lean
@[my_simp] theorem f_eq : f x = x + 2 := rfl
@[my_simp] theorem g_eq : g x = x + 1 := rfl

example : f x + g x = 2*x + 3 := by
  simp_arith -- does not appy f_eq and g_eq
  simp_arith [f, g]

example : f x + g x = 2*x + 3 := by
  simp_arith [my_simp]

example : f x = id (x + 2) := by
  simp
  simp [my_simp]
```

## Using `dummy_attr`

We'll see you at [`./attrs/dummy.lean`](./attrs/dummy.lean).


We run the `dummy_attr <number>`, and we see that we get access to the
attribute argument <number>, the name of the declaration (`foo`), the type
of the declaration (`int`), and the value of the declaration, which
is the raw syntax tree.

```lean
@[dummy_attr 0]
def foo : Int := 42
-- number + 1: 1
-- src: foo | stx: (Attr.dummy_attr "dummy_attr" (num "0")) | kind: global
-- srcDecl:
--   name: foo
--   type: Int
--   value?: (some (OfNat.ofNat.{0} Int 42 (Int.instOfNatInt 42)))
```

Below is an example of a declaration that does not have any value.

```lean
@[dummy_attr 52]
class bar 
-- number + 1: 53
-- src: bar | stx: (Attr.dummy_attr "dummy_attr" (num "52")) | kind: global
-- srcDecl:
--   name: bar
--   type: Type
--   value?: none
```

## Modifying the `value` with the `around` attribute

We're going to write an attribute that will modify a given definition


## Implementing `sym`:
Scoped environment extension maintains scoping information, so it keeps track of
whether the tag is local or not.
