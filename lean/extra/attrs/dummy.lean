import Lean
open Lean

namespace Attr
syntax (name := dummy_attr) "dummy_attr" term : attr
initialize registerTraceClass `dummy_attr

initialize registerBuiltinAttribute {
    name := `dummy_attr
    descr :="dummy_attr print information"
    add := fun src stx kind => do
      let num : Nat := stx[1].toNat
      dbg_trace "number + 1: {num + 1}"
      dbg_trace "src: {src} | stx: {stx} | kind: {kind}"
      let srcDecl ← getConstInfo src
      dbg_trace "srcDecl:"
      dbg_trace "  name: {srcDecl.name}"
      dbg_trace "  type: {srcDecl.type}"
      dbg_trace "  value?: {srcDecl.value?}"
      return ()
  }

-- QUESTION: Can I uncomment this?
-- @[dummy_attr "foo"]
-- def foo : Int := 42

