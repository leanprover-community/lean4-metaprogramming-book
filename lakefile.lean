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

require "leanprover-community" / "batteries" @ git "main"

def runCmd (input : String) : IO Unit := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  if out.exitCode != 0 then
    IO.eprintln out.stderr
    throw <| IO.userError s!"Failed to execute: {input}"
  else if !out.stdout.isEmpty then
    IO.println out.stdout

/-- Get markdown files from Lean files -/
script mdbuild do
  runCmd "lake exe mdgen lean md"
  return 0

/-- Get HTML files from Lean files.
This script is useful when rewriting a book while previewing it with `mdbook serve`. -/
script build do
  runCmd "lake exe mdgen lean md"
  runCmd "mdbook build"
  return 0
