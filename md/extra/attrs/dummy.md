```lean
import Lean
open Lean

namespace Attr
syntax (name := dummy_attr) "dummy_attr" term : attr
```

This uses a low level attribute registration function. We declare the attribute
with `registerBuiltinAttribute`. The `name` field is the name of the attribute, which
should match with the `syntax` above for parsing. The `descr` is the textual description
of the attribute used for docstrings. The `add` function is run when the attribute is applied to a
declaration of name `declName`. `stx` is the syntax of the attribute including arguments

```lean
initialize registerBuiltinAttribute {
    name := `dummy_attr
    descr :="dummy_attr print information"
    add := fun declName stx kind => do
      let num : Nat := stx[1].toNat
      dbg_trace "number + 1: {num + 1}"
      dbg_trace "declName: {declName} | stx: {stx} | kind: {kind}"
      let srcDecl ← getConstInfo declName
      dbg_trace "srcDecl:"
      dbg_trace "  name: {srcDecl.name}"
      dbg_trace "  type: {srcDecl.type}"
      dbg_trace "  value?: {srcDecl.value?}"
      return ()
  }
```
