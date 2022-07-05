import Lake
open Lake DSL

package «lean4-metaprogramming-book» {
  srcDir := "lean"
  isLeanOnly := true
}

@[defaultTarget]
lean_lib «lean4-metaprogramming-book» {
  roots := #["cover"]
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

script viper_build do
  let _ ← runCmd "rm" #["-rf", "md"]

  if ← runCmd "viper" #["-m", "lean2md", "lean", "md"] then return 1
  if ← runCmd "viper" #["-m", "lean2md", "lean/main", "md/main"] then return 1
  if ← runCmd "viper" #["-m", "lean2md", "lean/extra", "md/extra"] then return 1

  return 0
