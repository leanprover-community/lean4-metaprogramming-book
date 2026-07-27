import Lean
import Lean.Parser.Syntax
import Batteries.Util.ExtendedBinder

open Lean Elab Command Term

/- ## `Syntax`: Solutions -/

/- ### 1. -/

namespace a
  scoped notation:71 lhs:50 " 💀 " rhs:72 => lhs - rhs

  #guard 5 * 8 💀 4 = 20
  #guard 8 💀 6 💀 1 = 1
end a

namespace b
  set_option quotPrecheck false
  scoped infixl:71 " 💀 " => fun lhs rhs => lhs - rhs

  #guard 5 * 8 💀 4 = 20
  #guard 8 💀 6 💀 1 = 1
end b

namespace c
  scoped syntax:71 term:50 " 💀 " term:72 : term
  scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)

  #guard 5 * 8 💀 4 = 20
  #guard 8 💀 6 💀 1 = 1
end c

/- ### 2. -/

syntax "good" "morning" : term
syntax "hello" : command
syntax "yellow" : tactic

-- Note: the following are highlighted in red, however that's just because we haven't implemented the semantics ("elaboration function") yet - the syntax parsing stage works.

/--
info: elaboration function for 'termGoodMorning' has not been implemented
  good morning
-/
#guard_msgs in --#
#check_failure good morning

/-- error: elaboration function for 'commandHello' has not been implemented -/
#guard_msgs in --#
hello -- the syntax parsing stage works

/-- error: tactic 'tacticYellow' has not been implemented -/
#guard_msgs in --#
example : 2 + 2 = 4 := by
  yellow -- the syntax parsing stage works

/-- info: unknown identifier 'yellow' -/
#guard_msgs in --#
#check_failure yellow

/- ### 3. -/

syntax (name := colors) (("blue"+) <|> ("red"+)) num : command

@[command_elab colors]
def elabColors : CommandElab := fun _stx => Lean.logInfo "success!"

/-- info: success! -/
#guard_msgs in --#
blue blue 443

/-- info: success! -/
#guard_msgs in --#
red red red 4

/- ### 4. -/

syntax (name := help) "#better_help" "option" (ident)? : command

@[command_elab help]
def elabHelp : CommandElab := fun _stx => Lean.logInfo "success!"

/-- info: success! -/
#guard_msgs in --#
#better_help option

/-- info: success! -/
#guard_msgs in --#
#better_help option pp.r

/-- info: success! -/
#guard_msgs in --#
#better_help option some.other.name

/- ### 5. -/

-- Note: Batteries has to be in dependencies of your project for this to work.
syntax (name := bigsumin) "∑ " Batteries.ExtendedBinder.extBinder "in " term "," term : term

@[term_elab bigsumin]
def elabSum : TermElab := fun _stx _tp =>
  return mkNatLit 666

#guard (∑ x in { 1, 2, 3 }, x^2) = 666

def hi := (∑ x in { "apple", "banana", "cherry" }, x.length) + 1
#guard hi = 667
