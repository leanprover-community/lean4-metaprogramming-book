import Lean
import Lean.Parser.Syntax
import Std.Util.ExtendedBinder

open Lean Elab Command Term

/- ## `Syntax`: Solutions -/

/- ### 1. -/

namespace a
  scoped notation:71 lhs:50 " 💀 " rhs:72 => lhs - rhs
end a

namespace b
  set_option quotPrecheck false
  scoped infixl:71 " 💀 " => fun lhs rhs => lhs - rhs
end b

namespace c
  scoped syntax:71 term:50 " 💀 " term:72 : term
  scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)
end c

open a
#eval 5 * 8 💀 4 -- 20
#eval 8 💀 6 💀 1 -- 1

/- ### 2. -/

syntax "good morning" : term
syntax "hello" : command
syntax "yellow" : tactic

-- Note: the following are highlighted in red, however that's just because we haven't implemented the semantics ("elaboration function") yet - the syntax parsing stage works.

#check_failure good morning -- the syntax parsing stage works

/-- error: elaboration function for 'commandHello' has not been implemented -/
#guard_msgs in --#
hello -- the syntax parsing stage works

/-- error: tactic 'tacticYellow' has not been implemented -/
#guard_msgs in --#
example : 2 + 2 = 4 := by
  yellow -- the syntax parsing stage works

#check_failure yellow -- error: `unknown identifier 'yellow'`

/- ### 3. -/

syntax (name := colors) (("blue"+) <|> ("red"+)) num : command

@[command_elab colors]
def elabColors : CommandElab := fun stx => Lean.logInfo "success!"

blue blue 443
red red red 4

/- ### 4. -/

syntax (name := help) "#better_help" "option" (ident)? : command

@[command_elab help]
def elabHelp : CommandElab := fun stx => Lean.logInfo "success!"

#better_help option
#better_help option pp.r
#better_help option some.other.name

/- ### 5. -/

-- Note: std4 has to be in dependencies of your project for this to work.
syntax (name := bigsumin) "∑ " Std.ExtendedBinder.extBinder "in " term "," term : term

@[term_elab bigsumin]
def elabSum : TermElab := fun stx tp =>
  return mkNatLit 666

#eval ∑ x in { 1, 2, 3 }, x^2

def hi := (∑ x in { "apple", "banana", "cherry" }, x.length) + 1
#eval hi
