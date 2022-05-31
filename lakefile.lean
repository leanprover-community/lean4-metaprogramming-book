import Lake
open Lake DSL

package «lean4-metaprogramming-book» {
  defaultFacet := PackageFacet.oleans
}

def runCmd (cmd : String) (args : Array String) : ScriptM Bool := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  let hasError := out.exitCode != 0
  if hasError then
    IO.eprint out.stderr
  return hasError

script build do
  let _ ← runCmd "rm" #["-rf", "md"]

  if ← runCmd "python" #["-m", "lean2md", "lean", "md"] then return 1
  if ← runCmd "python" #["-m", "lean2md", "lean/main", "md/main"] then return 1
  if ← runCmd "python" #["-m", "lean2md", "lean/extra", "md/extra"] then return 1

  return 0