```lean
import Lean
open Lean

-- The name of the syntax is important. The name is
-- used to connect to the corresponding attribute.
syntax (name := myParam) "myParam" num "important"? : attr
```

This declarares the attribute `myParamAttr`, which is parametrized
by a value of type `(Nat × Bool)`. The `getParam` function describes how to build
a value of `(Nat × Bool)` given the raw syntax declared by `myParam` above.
The `afterSet` function can be used as a finalizer to perform processing once we have
a parsed value.

initialize fooParamAttr : ParametricAttribute (Nat × Bool) ←
  registerParametricAttribute {
    name := `myParam  /-
       The attribute name must match the `syntax` declaration name.

```lean
descr := "parametric attribute containing a priority and flag"
    getParam := fun _ stx =>
      match stx with
      | `(attr| myParam $prio:num) =>
          return (prio.getNat, false)
      | `(attr| myParam $prio:num important) =>
          return (prio.getNat, true)
      | _  => throwError "unexpected foo attribute"
    afterSet := fun declName val => do
      IO.println s!"set attribute [myParam] at {declName}; priority: {val.1}; important? {val.2}"
  }
```
