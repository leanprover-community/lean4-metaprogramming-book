import Lake
open Lake DSL

package «lean4-metaprogramming-book» {
  -- add configuration options here
}

script build do
  let _ ← IO.Process.output {
    cmd := "rm"
    args := #["-rf", "md"]
  }
  let out ← IO.Process.output {
    cmd := "python"
    args := #["-m", "lean2md", "lean/main", "md/main"]
  }
  if out.exitCode ≠ 0 then
    IO.eprint out.stderr
    return 1
  let out ← IO.Process.output {
    cmd := "python"
    args := #["-m", "lean2md", "lean/extra", "md/extra"]
  }
  if out.exitCode ≠ 0 then
    IO.eprint out.stderr
    return 1
  return 0