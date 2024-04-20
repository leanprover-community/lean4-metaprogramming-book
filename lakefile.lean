import Lake
open Lake DSL

package «lean4-metaprogramming-book» where
  srcDir := "lean"

@[default_target]
lean_lib «lean4-metaprogramming-book» where
  roots := #[`cover, `extra, `main, `solutions]
  globs := #[Glob.one `cover, Glob.submodules `extra, Glob.submodules `main, Glob.submodules `solutions]

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "v1.3.0"

require std from git "https://github.com/leanprover/std4" @ "v4.7.0"

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
  if ← runCmd "lake" #["exe", "mdgen", "lean", "md"] then return 1
  return 0
