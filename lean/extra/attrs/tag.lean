import Lean

open Lean Meta System Std Elab Command


initialize myTagAttribute : TagAttribute ←
  registerTagAttribute `myTag "We are testing this custom tag."


def listAllTagged : MetaM Unit := do
    let env <- getEnv
    for declName in myTagAttribute.ext.getState env do
      let mval := env.find? declName
      let mstr := match mval with | .none => "<none>" | .some v => toString v.value!
      dbg_trace "decl: {declName} | find? {mstr}"
    -- let x : NameSet := myTagAttribute.ext.getState env


elab "listAllTagged" : command => do
  liftTermElabM (some `listAllTagged) (listAllTagged)
  return ()
   
  


