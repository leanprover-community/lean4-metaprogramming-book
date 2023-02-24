import Lean
import Lean.Parser.Syntax

open Lean Elab Command Term

/- ## `Syntax`: Solutions -/

/-
1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.
-/

namespace a
  scoped notation:71 lhs:50 " 💀 " rhs:72 => lhs - rhs
end a

namespace b
  set_option quotPrecheck false
  scoped infixl:71 " 💀 " => λ lhs rhs => lhs - rhs
end b

namespace c
  scoped syntax:71 term:50 " 💀 " term:72 : term
  scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)
end c

open a
#eval 5 * 8 💀 4 -- 20
#eval 8 💀 6 💀 1 -- 1

/-
2. Consider the following syntax categories: `term`, `command`, `tactic`; and 3 syntax rules given below. Make use of each of these newly defined syntaxes.
-/

syntax "good morning" : term
syntax "hello" : command
syntax "yellow" : tactic

-- Note: the following are highlighted in red, however that's just because we haven't implemented the semantics ("elaboration function") yet - the syntax parsing stage works.

#eval good morning -- works
-- good morning -- error: `expected command`

hello -- works
-- #eval hello -- error: `expected term`

example : 2 + 2 = 4 := by
  yellow -- works
-- yellow -- error: `expected command`
-- #eval yellow -- error: `unknown identifier 'yellow'`

/-
3. Create a `syntax` rule that would accept the following commands:

- `red red red 4`
- `blue 7`
- `blue blue blue blue blue 18`

Use the following code template:

```
syntax (name := colors) ...
-- our "elaboration function" that infuses syntax with semantics
@[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
```
-/

syntax (name := colors) (("blue"+) <|> ("red"+)) num : command

@[command_elab colors]
def elabColors : CommandElab := λ stx => Lean.logInfo "success!"

blue blue 443
red red red 4

/-
4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.

Create a `syntax` rule that would accept the following commands:

- `#better_help option`
- `#better_help option pp.r`
- `#better_help option some.other.name`
-/

syntax (name := help) "#better_help" "option" (ident)? : command

@[command_elab help]
def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"

#better_help option
#better_help option pp.r
#better_help option some.other.name

/-
5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:

- `∑ x in { 1, 2, 3 }, x^2`
- `∑ x in { "apple", "banana", "cherry" }, x.length`
-/

-- Note: std4 has to be in dependencies of your project for this to work.
syntax (name := bigsumin) "∑ " Std.ExtendedBinder.extBinder "in " term "," term : term

@[term_elab bigsumin]
def elabSum : TermElab := λ stx tp =>
  return mkNatLit 666

#eval ∑ x in { 1, 2, 3 }, x^2

def hi := (∑ x in { "apple", "banana", "cherry" }, x.length) + 1
#eval hi
