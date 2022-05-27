/-
## DSLs in Lean

In this tutorial, we shall write a DSL for [IMP](http://concrete-semantics.org/concrete-semantics.pdf),
which is a simple imperative language.
-/
import Lean
import Lean.Elab.Deriving.Basic
open Lean Lean.Syntax
open Lean.Elab
open Lean.Elab.Command
open Lean.Meta
open Lean

/--
We begin by defining the AST of the language:
-/

abbrev vname := String

inductive Aexp 
| ANat: Nat -> Aexp
| AVar: String -> Aexp
| APlus: Aexp -> Aexp -> Aexp
deriving Inhabited

inductive Bexp
| BBool: Bool -> Bexp
| BVar: String -> Bexp
| BAnd: Bexp -> Bexp -> Bexp
| BLess: Aexp -> Aexp -> Bexp
deriving Inhabited

inductive Command
| Skip: Command
| Assign: vname -> Aexp -> Command
| Seq: Command -> Command -> Command
| If: Bexp -> Command -> Command
| While: Bexp -> Command
deriving Inhabited


/-
## Direct parsing by macros
-/

/-
#### Parsing aexp 
-/

declare_syntax_cat imp_aexp
syntax num : imp_aexp
syntax ident : imp_aexp
syntax imp_aexp "+" imp_aexp : imp_aexp

syntax "[imp_aexp|" imp_aexp "]" : term

macro_rules
| `([imp_aexp| $n:num ]) => do
   let n : Nat := n.toNat
   let nStx : Syntax := Lean.quote n
   `(Aexp.ANat $(nStx))

def example_aexp_num: Aexp := [imp_aexp| 42]
#reduce example_aexp_num
-- Aexp.ANat 42

macro_rules
| `([imp_aexp| $name:ident ]) => do
   let nameStr : String := name.getId.toString
   let nameStx : Syntax := Lean.quote nameStr
   `(Aexp.AVar $(nameStx))


def example_aexp_ident: Aexp := [imp_aexp| foo]
#reduce example_aexp_ident
-- Aexp.AVar "foo"

macro_rules
| `([imp_aexp| $x:imp_aexp + $y:imp_aexp]) => do
      let xStx <- `([imp_aexp| $(x)])
      let yStx <- `([imp_aexp| $(y)])
      `(Aexp.APlus $xStx $yStx)

def example_aexp_plus: Aexp := [imp_aexp| foo + bar]
#reduce example_aexp_plus
-- Aexp.APlus (Aexp.AVar "foo") (Aexp.AVar "bar")

/-
#### Parsing BExp

We repeat the same process, this time for `BExp`.
-/

declare_syntax_cat imp_bexp
syntax ident : imp_bexp

/-
Note that we want `<` to have lower precedence than `+`,
whch we declare by annotating the parse rule with `syntax:min`. 
-/

/-
Once again, we declare the macro `[imp_bexp|...]` which takes
an `imp_exp` and produces a Lean `term`.
-/
syntax "[imp_bexp| " imp_bexp "]" : term

/-
We write the macro rule once more:
-/

macro_rules
| `([imp_bexp| $x:ident]) => do 
    let xStr : String := x.getId.toString
    match xStr with 
    | "true" => `(Bexp.BBool true)
    | "false" => `(Bexp.BBool false)
    | _ => do
       let xStx : Syntax := quote xStr
       `(Bexp.BVar $xStx)
  
def example_bexp_true : Bexp := [imp_bexp| true]
#print example_bexp_true 
-- BExp.BBool true

def example_bexp_false : Bexp := [imp_bexp| false]
#print example_bexp_false
-- BExp.BBool false

def example_bexp_ident : Bexp := [imp_bexp| var]
#print example_bexp_ident
-- BExp.BVar "var"


syntax:min imp_aexp "<" imp_aexp : imp_bexp 


macro_rules
| `([imp_bexp| $x:imp_aexp < $y:imp_aexp]) =>
      `(Bexp.BLess [imp_aexp| $x] [imp_aexp| $y])

def example_bexp_lt_1 : Bexp := [imp_bexp| 1 < 2]
#print example_bexp_lt_1
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

def example_bexp_lt_2 : Bexp := [imp_bexp| 1 + 1 < 2 + 2]
#print example_bexp_lt_2
-- Bexp.BLess (Aexp.ANat 1) (Aexp.ANat 2)

syntax imp_bexp "&&" imp_bexp : imp_bexp
macro_rules
| `([imp_bexp| $x:imp_bexp && $y:imp_bexp]) => do
    `(Bexp.Band [imp_bexp| $x] [imp_bexp| $y])

def example_bexp_and_1: Bexp := [imp_bexp| true && true]
#print example_bexp_and_1

/-
#### Parsing commands
-/

declare_syntax_cat imp_command
syntax ident "=" imp_aexp : imp_command
syntax sepBy(imp_command, ";") : imp_command

/- 
## Greater type checking: Parsing by going through Syntax -> Except String
-/

-- Helper to lift applicative function
private def liftA2 {α β γ : Type} [Applicative f] (g: α → β → γ) (fa: f α) (fb: f β): f γ :=
  Applicative.toSeq.seq (Functor.map g fa)  (fun () => fb)

partial def mkAexp : Syntax → Except String Aexp
  | `(imp_aexp| $i:num ) => return Aexp.ANat i.toNat
  | `(imp_aexp| $name:ident ) => return Aexp.AVar name.getId.toString
  | `(imp_aexp| $x:imp_aexp + $y:imp_aexp) => 
      liftA2 Aexp.APlus (mkAexp x) (mkAexp y)
  | x => throw "error parsing expression statement {x}"



-- | TODO: handle precedence
partial def mkBexp : Syntax → Except String Bexp
  | `(imp_bexp| $name:ident ) => 
     return Bexp.BVar name.getId.toString
  | `(imp_bexp| $x:imp_aexp < $y:imp_aexp) => 
      liftA2 Bexp.BLess (mkAexp x) (mkAexp y)
  | `(imp_bexp| $x:imp_bexp && $y:imp_bexp) => 
      liftA2 Bexp.BAnd (mkBexp x) (mkBexp y)
  | x => throw "error parsing expression statement {x}"


class QuoteM (a: Type) where
  quoteM : a -> MacroM Syntax
open QuoteM

instance [Quote a] : QuoteM a where
  quoteM a := return (quote a)


-- abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)

def runMacroM (defaultA: a) (ma: MacroM a): a :=
  let estate := ReaderT.run ma (Macro.Context.mk default `syntheticMainModule 0 0 99999 Syntax.missing)
  let aopt := estate.run' (Macro.State.mk 0 [])
  aopt.getD defaultA

def quoteMAexp : Aexp → MacroM Syntax
 | .ANat n => `(Aexp.ANat $(quote n))
 | .AVar v => `(Aexp.AVar $(quote v))
 | .APlus l r => do 
     let ql <- quoteMAexp l
     let qr <- quoteMAexp r 
     `(Aexp.APlus $(ql) $(qr))

instance : QuoteM Aexp where
  quoteM := quoteMAexp


-- Convert a parser from (Syntax → α) into a parser (Syntax → Syntax)
def quotedParser [Quote α] (p: Syntax -> Except ε α): Syntax -> Except ε Syntax :=
   (Functor.map quote) ∘ p



def quoteMBexp : Bexp → MacroM Syntax
 | .BBool b => `(BExp.BBool $(quote b))
 | .BVar v => `(BExp.BVar $(quote v))
 | .BLess l r => `(BExp.BLess $(quote l) $(quote r))
 | .BAnd l r => `(BExp.BAnd $(quote l) $(quote r))



-- def quoteMTerm : Term -> MacroM Syntax
-- | .negation t => do
--      `(Term.negation $(<- (quoteMTerm t)))
-- | .logical_negation t => do
--      `(Term.logical_negation $(<- (quoteMTerm t)))
-- | .const c => do
--   `(Term.const $(<- (quoteM c)))
-- | _ => Macro.throwError "unhandled term case"
-- 
-- instance : QuoteM Term where
--   quoteM := quoteMTerm
-- 
-- instance [Inhabited a] [QuoteM a] : Quote a where
--   quote (val: a) := runMacroM default (quoteM val)

-- macro_rules
--   | `([constval| $x:constval ]) => do
--       
--      let val := mkConstval x
--      match val with
--        | .error msg => Macro.throwError msg
--        | .ok v => return (quote v)
-- 
-- 
-- macro_rules
-- | `([dsl_term| $x ]) => do
--    let val := mkTerm x
--    match val with
--    | .error msg => Macro.throwError msg
--    | .ok v => return (quote v)



-- | run a parser `p` for syntax category `syntaxcat`, to interpret the string `s`  
-- in environment `e` into a term of type α.
private def mkParseFun {α : Type} (syntaxcat : Name) 
  (p : Syntax → Except String α)
  (s: String)
  (env: Environment): Except String α := do
  p (← Parser.runParserCategory env syntaxcat s)

-- | Run mkParseFun, extract the error, and always provide an α
-- using the inhabited instance.
private def mkNonTerminalParser {α : Type} [Inhabited α] 
  (syntaxcat : Name)
  (p : Syntax → Except String α)
  (s : String)
  (env : Environment): Option String × α :=
  let parseFun := mkParseFun syntaxcat p
  match parseFun s env with
    | .error msg => (some msg, default)
    | .ok    p   => (none, p)


-- private def liftExcept3 {α β γ δ : Type} : (α → β → γ → δ) → Except String α → Except String β →
-- Except String γ → Except String δ :=
--   λ f a b c => do
--   match a with
--   | .error msg => .error msg
--   | .ok r₁ => match b with
--     | .error msg => .error msg
--     | .ok r₂ => match c with
--       | .error msg => .error msg
--       | .ok r₃ => return f r₁ r₂ r₃

/-
mutual
partial def mkConstval : Syntax → Except String Const
| `(constval| $x:num ) => return Const.num_lit x.toNat
| `(constval| $x:str ) => match x.isStrLit? with
  | some s => return Const.str_lit s
  | none   => unreachable! -- because of `s:str`
| _ => throw "error parsing constant value"


partial def mkUnuaryop : Syntax → Except String Term
  | `(unuaryop| -$x) => liftExcept Term.negation (mkTerm x)
  -- | `(unuaryop| ~$x) => Term.logical_negation x
  -- | `(unuaryop| !$x) => Term.binary_negation x
  | _ => throw "error parsing unuary operator (not implemented)"

partial def mkQualifiedName : Syntax → Except String QualifiedName
  | `(qualified_name| $x:ident $[. $xs:ident ]* ) => do
    let xStr : String := x.getId.toString
    let xsList <- xs.foldrM (init := [xStr]) fun x xs => return (x.getId.toString :: xs)
    return QualifiedName.mk xsList
  | _ => throw "error parsing qualified name"

partial def mkExprList : Syntax → Except String (List Expr)
  | `(expr_list| $exprs:expr,*) => do
    let joinFun := fun x xs => do -- lift this pattern into a HOF
      let res := mkExpr x
      match res with
        | .error msg => .error msg
        | .ok exp => return (exp::xs)
    let valList <- exprs.getElems.foldrM (init := []) joinFun
    return valList
  | _ => throw "error parsing expression list"

partial def mkExpr : Syntax → Except String Expr
  | `(expr| $x:unuaryop ) => liftExcept Expr.some_term $ mkUnuaryop x
  | `(expr| $x:binop ) => mkBinop x
  | `(expr| $x:parexpr ) => mkParExpr x
  -- | `(expr| $x:list ) => liftExcept Expr.list mkList x
  | `(expr| $x:dsl_term ) => liftExcept Expr.some_term $ mkTerm x
  | _ => throw "error, parser unimplemented"

partial def mkParExpr : Syntax → Except String Expr
  | `(parexpr| ($e:expr)) => mkExpr e
  | _ => throw "error parsing expression in parenthesis"

partial def mkBinop : Syntax → Except String Expr
  | `(binop| $x:dsl_term + $y:dsl_term ) => liftExcept2 Expr.add (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term - $y:dsl_term ) => liftExcept2 Expr.sub (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term * $y:dsl_term ) => liftExcept2 Expr.mul (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term / $y:dsl_term ) => liftExcept2 Expr.div (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term & $y:dsl_term ) => liftExcept2 Expr.binand (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term | $y:dsl_term ) => liftExcept2 Expr.binor (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term ^ $y:dsl_term ) => liftExcept2 Expr.binxor (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term << $y:dsl_term ) => liftExcept2 Expr.leftshift (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term >> $y:dsl_term ) => liftExcept2 Expr.rightshift (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term < $y:dsl_term ) => liftExcept2 Expr.less_than (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term > $y:dsl_term ) => liftExcept2 Expr.greater_than (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term <= $y:dsl_term ) => liftExcept2 Expr.leq (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term >= $y:dsl_term ) => liftExcept2 Expr.geq (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term == $y:dsl_term ) => liftExcept2 Expr.equal (mkTerm x) (mkTerm y)
  | `(binop| $x:dsl_term != $y:dsl_term ) => liftExcept2 Expr.not_equal (mkTerm x) (mkTerm y)
  | _ => throw "error parsing binary operator"


partial def mkCall : Syntax → Except String Term
  | `(call| $n:qualified_name ( $e:expr_list )  ) =>
    liftExcept2 Term.function_call (mkQualifiedName n) (mkExprList e)
  | _ => throw "error parsing function call"

partial def mkTerm : Syntax → Except String Term
  | `(dsl_term|  $c:constval ) => liftExcept (λ const => Term.const const) (mkConstval c)
  | `(dsl_term|  $i:ident ) => match i.isIdent with
    | true => Except.ok $ Term.var i.getId.toString
    | false => Except.error "error parsing variable"
  | `(dsl_term|  $n:qualified_name ) => liftExcept (λ x => Term.qualified_var x) (mkQualifiedName n)
  | `(dsl_term|  $c:call ) => mkCall c
  | _ => throw "error parsing term"

partial def mkTypedIdentifier : Syntax → Except String TypedIdentifier
  | `(typed_identifier| $t:ident $x:ident ) => do
    let tStr : String := t.getId.toString
    let xStr : String := x.getId.toString
    return TypedIdentifier.mk tStr xStr
  | _ => throw "error parsing typed identifier"

-- this is a really weird behavior, why won't it work with `(declaration | $x:structure_declaration) ?
partial def mkDescription : Syntax → Except String Description
  | `(structure_declaration| $x:structure_declaration ) => mkStructureDeclaration x
  | `(internal_func_decl| $x:internal_func_decl ) => mkInternalFuncDecl x
  | _ => throw "error parsing declaration"

partial def mkVariableDeclaration : Syntax → Except String Statement
  | `(variable_declaration| $x:typed_identifier = $e ) => liftExcept2 Statement.value_declaration (mkTypedIdentifier x) (mkExpr e)
  | `(variable_declaration| $x:typed_identifier) => liftExcept Statement.variable_declaration (mkTypedIdentifier x)
  | _ => throw "error parsing variable declaration"

partial def mkLabeledStatement : Syntax → Except String Statement
  | `(labeled_statement| $l:label $s ) => liftExcept2 Statement.labelled_statement (mkLabel l) (mkStatement s)
  | _ => throw "error parsing labeled statement"

partial def mkLabel : Syntax → Except String Label
  | `(label| result_write ) => return Label.result_write
  | _ => throw "error parsing label"

partial def mkAssigmnent : Syntax → Except String Statement
  | `(assignment| $q:qualified_name = $e ) => liftExcept2 Statement.variable_assignment (mkQualifiedName q) (mkExpr e)
  | `(assignment| $i:ident = $e ) => let name := (QualifiedName.mk [i.getId.toString])
    liftExcept (Statement.variable_assignment name) (mkExpr e)
  | _ => throw "error parsing assignment"

partial def mkConditional : Syntax → Except String Conditional
  | `(conditional| if ( $e ) $s else $es ) => liftExcept3 Conditional.if_else_statement
    (mkExpr e) (mkStatement s) (mkStatement es)
  | `(conditional| if ( $e ) $s ) => liftExcept2 Conditional.if_statement (mkExpr e) (mkStatement s)
  | _ => throw "error parsing assignment"

partial def mkBlock : Syntax → Except String Statement
  | `(block| { $[ $stmts ]* }) => do
    let stmtList <- stmts.foldrM (init := []) fun x xs => do
      let s <- mkStatement x
      return s::xs
    return Statement.block stmtList
  | _ => throw "error parsing block statement"


partial def mkAwaitBlock : Syntax → Except String Statement
| `(await_block| await { $w }) => liftExcept Statement.await (mkStatement w)
| _ => throw "error parsing await block statement"

partial def mkWhenBlock : Syntax → Except String Statement
| `(when_block| when ($n) { $stmt }) => liftExcept2 Statement.when
  (mkQualifiedName n) (mkStatement stmt)
  | _ => throw "error parsing when block statement"

partial def mkTryCatch : Syntax → Except String Statement
  | `(try_catch| try $s:statement $[ $c:catch_block ]* ) => do -- why doesn't the '+' pattern work?
    let catchList <- c.foldrM (init := []) fun x xs => do
      let cb <- mkCatchBlock x
      return (cb::xs)
    liftExcept (λ stmt => Statement.try_catch stmt catchList) (mkStatement s)
  | _ => throw "error parsing try-catch statement"

partial def mkCatchBlock : Syntax → Except String CatchBlock
  | `(catch_block| catch ( $n ) $s:statement ) => liftExcept2 CatchBlock.mk
    (mkQualifiedName n) (mkStatement s)
  | _ => throw "error parsing catch block"

partial def mkStatement : Syntax → Except String Statement
  | `(statement| $x:labeled_statement $[;]? ) => mkLabeledStatement x
  | `(statement| $x:dsl_transition $[;]? ) => mkTransition x
  | `(statement| $x:variable_declaration $[;]? ) => mkVariableDeclaration x
  | `(statement| $x:assignment $[;]? ) => mkAssigmnent x
  | `(statement| $x:conditional $[;]? ) => liftExcept Statement.conditional_stmt (mkConditional x) -- feels unnecessary
  | `(statement| $x:block $[;]? ) => mkBlock x
  | `(statement| $x:await_block $[;]? ) => mkAwaitBlock x
  | `(statement| $x:try_catch $[;]? ) => mkTryCatch x
  | `(statement| $x:return_stmt $[;]? ) => mkReturnStmt x
  | `(statement| $x:expr $[;]? ) => liftExcept Statement.stray_expr (mkExpr x)
  | _ => throw "error parsing statement"

partial def mkReturnStmt : Syntax → Except String Statement
  | `(return_stmt| return $e ) => liftExcept Statement.return_stmt (mkExpr e)
  | _ => throw "error parsing return statement"

partial def mkTransition : Syntax → Except String Statement
  | `(dsl_transition| transition $i ) => return Statement.transition i.getId.toString
  | _ => throw "error parsing transition statement"

partial def mkList : Syntax → Except String Expr
  | `(list| [$e:expr_list] ) => liftExcept Expr.list (mkExprList e)
  | _ => throw "error parsing expression list"

partial def mkStructureDeclaration : Syntax → Except String Description
  | `(structure_declaration| controller $id:ident $s ) =>
    liftExcept (Description.controller id.getId.toString) (mkStatement s)
  | `(structure_declaration| state_queue $id:ident $s ) => -- TODO: difference to controller?
    liftExcept (Description.controller id.getId.toString) (mkStatement s)
  | `(structure_declaration| controller_entry $id:ident $s ) =>
    liftExcept (Description.entry id.getId.toString) (mkStatement s)
  | `(structure_declaration| controller_control_flow $id:ident $s ) =>
    liftExcept (Description.control_flow id.getId.toString) (mkStatement s)
  | `(structure_declaration| transition $id:ident $s:statement) =>
    liftExcept (Description.transition id.getId.toString) (mkStatement s)
  | _ => throw "error parsing structure declaration"

partial def mkInternalFuncDecl : Syntax → Except String Description
  | `(internal_func_decl| $id:typed_identifier ( $args ){ $s }) =>
    liftExcept3 Description.function_definition (mkTypedIdentifier id) (mkArgList args) (mkStatement s)
  | _ => throw "error parsing internal function declaration"

partial def mkArgList : Syntax → Except String (List TypedIdentifier)
  | `(arg_list| $fst:typed_identifier $rest,*) => do
      let initId <- mkTypedIdentifier fst
      let argList <- rest.getElems.foldrM (init := [initId]) fun x xs => do
        let xid <- mkTypedIdentifier x
        return (xid::xs)
      return argList
  | _ => throw "error parsing argument list"

partial def mkAST : Syntax → Except String AST
  | `(file|$[$decls:declaration]*) => do
    let declList <- decls.foldrM (init := []) fun x xs => do
      let desc <- mkDescription x
      return (desc::xs)
    return AST.structure_descriptions declList
  | _ => throw "error: can't parse file"
end

-- eDSL

syntax "[file|" file "]" : term
syntax "[statement|" statement "]" : term
syntax "[expr|" expr "]" : term
syntax "[typed_identifier|" typed_identifier "]" : term
syntax "[qualified_name|" qualified_name "]" : term
syntax "[declaration|" declaration "]" : term
syntax "[variable_declaration|" variable_declaration "]" : term
syntax "[labeled_statement|" labeled_statement "]" : term
syntax "[label|" label "]" : term
syntax "[assignment|" assignment "]" : term
syntax "[conditional|" conditional "]" : term
syntax "[block|" block "]" : term
syntax "[await_block|" await_block "]" : term
syntax "[when_block|" when_block "]" : term
syntax "[try_catch|" try_catch "]" : term
syntax "[catch_block|" catch_block "]" : term
syntax "[return_stmt|" return_stmt "]" : term
syntax "[dsl_term|" dsl_term "]" : term
syntax "[call|" call "]" : term
syntax "[unuaryop|" unuaryop "]" : term
syntax "[binop|" binop "]" : term
syntax "[expr_list|" expr_list "]" : term
syntax "[parexpr|" parexpr "]" : term
syntax "[list|" list "]" : term
syntax "[structure_declaration|" structure_declaration "]" : term
syntax "[internal_func_decl|" internal_func_decl "]" : term
syntax "[arg_list|" arg_list "]" : term
syntax "[constval|" constval "]" : term
syntax "[dsl_transition|" dsl_transition "]" : term

class QuoteM (a: Type)  where
  quoteM : a -> MacroM Syntax

open QuoteM

instance [Quote a] : QuoteM a where
  quoteM a := return (quote a)


-- abbrev MacroM := ReaderT Macro.Context (EStateM Macro.Exception Macro.State)

def runMacroM (defaultA: a) (ma: MacroM a): a :=
  let estate := ReaderT.run ma (Macro.Context.mk default `syntheticMainModule 0 0 99999 Syntax.missing)
  let aopt := estate.run' (Macro.State.mk 0 [])
  aopt.getD defaultA

def quoteMConst : Const → MacroM Syntax
 | .num_lit n => `(Const.num_lit $(quote n))
 | .str_lit s => `(Const.str_lit $(quote s))



instance : QuoteM Const where
  quoteM := quoteMConst

def quoteMTerm : Term -> MacroM Syntax
| .negation t => do
     `(Term.negation $(<- (quoteMTerm t)))
| .logical_negation t => do
     `(Term.logical_negation $(<- (quoteMTerm t)))
| .const c => do
  `(Term.const $(<- (quoteM c)))
| _ => Macro.throwError "unhandled term case"

instance : QuoteM Term where
  quoteM := quoteMTerm

instance [Inhabited a] [QuoteM a] : Quote a where
  quote (val: a) := runMacroM default (quoteM val)


macro_rules
  | `([constval| $x:constval ]) => do
     let val := mkConstval x
     match val with
       | .error msg => Macro.throwError msg
       | .ok v => return (quote v)


macro_rules
| `([dsl_term| $x ]) => do
   let val := mkTerm x
   match val with
   | .error msg => Macro.throwError msg
   | .ok v => return (quote v)


def foo := [constval| 42]     
#reduce foo

def bar := [dsl_term| 42]
#reduce bar
-/


-- CUSTOM DERIVING
/-
private abbrev IndexSet := Std.RBTree Nat compare
private abbrev LocalInst2Index := FVarIdMap Nat

private def implicitBinderF := Parser.Term.implicitBinder
private def instBinderF     := Parser.Term.instBinder

private def mkInhabitedInstanceUsing (inductiveTypeName : Name) (ctorName : Name) (addHypotheses : Bool) : CommandElabM Bool := do
  match (← liftTermElabM none mkInstanceCmd?) with
  | some cmd =>
    elabCommand cmd
    return true
  | none =>
    return false
where
  addLocalInstancesForParamsAux {α} (k : LocalInst2Index → TermElabM α) : List Expr → Nat → LocalInst2Index → TermElabM α
    | [], i, map    => k map
    | x::xs, i, map =>
      try
        let instType ← mkAppM `Inhabited #[x]
        if (← isTypeCorrect instType) then
          withLocalDeclD (← mkFreshUserName `inst) instType fun inst => do
            trace[Elab.Deriving.inhabited] "adding local instance {instType}"
            addLocalInstancesForParamsAux k xs (i+1) (map.insert inst.fvarId! i)
        else
          addLocalInstancesForParamsAux k xs (i+1) map
      catch _ =>
        addLocalInstancesForParamsAux k xs (i+1) map

  addLocalInstancesForParams {α} (xs : Array Expr) (k : LocalInst2Index → TermElabM α) : TermElabM α := do
    if addHypotheses then
      addLocalInstancesForParamsAux k xs.toList 0 {}
    else
      k {}

  collectUsedLocalsInsts (usedInstIdxs : IndexSet) (localInst2Index : LocalInst2Index) (e : Expr) : IndexSet :=
    if localInst2Index.isEmpty then
      usedInstIdxs
    else
      let visit {ω} : StateRefT IndexSet (ST ω) Unit :=
        e.forEach fun
          | Expr.fvar fvarId _ =>
            match localInst2Index.find? fvarId with
            | some idx => modify (·.insert idx)
            | none => pure ()
          | _ => pure ()
      runST (fun _ => visit |>.run usedInstIdxs) |>.2

  /- Create an `instance` command using the constructor `ctorName` with a hypothesis `Inhabited α` when `α` is one of the inductive type parameters
     at position `i` and `i ∈ assumingParamIdxs`. -/
  mkInstanceCmdWith (assumingParamIdxs : IndexSet) : TermElabM Syntax := do
    let indVal ← getConstInfoInduct inductiveTypeName
    let ctorVal ← getConstInfoCtor ctorName
    let mut indArgs := #[]
    let mut binders := #[]
    for i in [:indVal.numParams + indVal.numIndices] do
      let arg := mkIdent (← mkFreshUserName `a)
      indArgs := indArgs.push arg
      let binder ← `(implicitBinderF| { $arg:ident })
      binders := binders.push binder
      if assumingParamIdxs.contains i then
        let binder ← `(instBinderF| [ Inhabited $arg:ident ])
        binders := binders.push binder
    let type ← `(Inhabited (@$(mkIdent inductiveTypeName):ident $indArgs:ident*))
    let mut ctorArgs := #[]
    for i in [:ctorVal.numParams] do
      ctorArgs := ctorArgs.push (← `(_))
    for i in [:ctorVal.numFields] do
      ctorArgs := ctorArgs.push (← ``(Inhabited.default))
    let val ← `(⟨@$(mkIdent ctorName):ident $ctorArgs:ident*⟩)
    `(instance $binders:explicitBinder* : $type := $val)

  mkInstanceCmd? : TermElabM (Option Syntax) := do
    let ctorVal ← getConstInfoCtor ctorName
    forallTelescopeReducing ctorVal.type fun xs _ =>
      addLocalInstancesForParams xs[:ctorVal.numParams] fun localInst2Index => do
        let mut usedInstIdxs := {}
        let mut ok := true
        for i in [ctorVal.numParams:xs.size] do
          let x := xs[i]
          let instType ← mkAppM `Inhabited #[(← inferType x)]
          trace[Elab.Deriving.inhabited] "checking {instType} for '{ctorName}'"
          match (← trySynthInstance instType) with
          | LOption.some e =>
            usedInstIdxs := collectUsedLocalsInsts usedInstIdxs localInst2Index e
          | _ =>
            trace[Elab.Deriving.inhabited] "failed to generate instance using '{ctorName}' {if addHypotheses then "(assuming parameters are inhabited)" else ""} because of field with type{indentExpr (← inferType x)}"
            ok := false
            break
        if !ok then
          return none
        else
          trace[Elab.Deriving.inhabited] "inhabited instance using '{ctorName}' {if addHypotheses then "(assuming parameters are inhabited)" else ""} {usedInstIdxs.toList}"
          let cmd ← mkInstanceCmdWith usedInstIdxs
          trace[Elab.Deriving.inhabited] "\n{cmd}"
          return some cmd

private def mkInhabitedInstance (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let doIt (addHypotheses : Bool) : CommandElabM Bool := do
    for ctorName in indVal.ctors do
      if (← mkInhabitedInstanceUsing declName ctorName addHypotheses) then
        return true
    return false
  unless (← doIt false <||> doIt true) do
    throwError "failed to generate 'Inhabited' instance for '{declName}'"

def mkInhabitedInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    declNames.forM mkInhabitedInstance
    return true
  else
    return false

builtin_initialize
  registerBuiltinDerivingHandler `Inhabited mkInhabitedInstanceHandler
  registerTraceClass `Elab.Deriving.inhabited

-/
-- ^ END CUSTOM DERIVING

/-
-- parse functions
def parseConstval := mkNonTerminalParser `constval mkConstval
def parseCall := mkNonTerminalParser `call mkCall
def parseAssignment := mkNonTerminalParser `assignment mkAssigmnent
def parseStatement := mkNonTerminalParser `statement mkStatement
def parseDescription := mkNonTerminalParser `declaration mkDescription
def parseStructureDeclaration := mkNonTerminalParser `structure_declaration mkDescription
def parseExpr := mkNonTerminalParser `expr mkExpr
def parseFile := mkNonTerminalParser `file mkAST
def parse := parseFile
-/

/- 
# FAQ
-/
/-
#### How do I debug a `macro_rule`?

Use `dbg_trace` to print any information.
-/

syntax "[faq_debug|" term "]" :  term
macro_rules
| `([faq_debug| $x:term ]) => do 
      dbg_trace x
      return x

def faq_debug_example : Int := [faq_debug| 1 + 2 + 3]
-- («term_+_» («term_+_» (num "1") "+" (num "2")) "+" (num "3"))

/-
#### How do I throw an errror from a macro?

Use `MacroM.throw: String → MacroM α
-/

syntax "[faq_error|" term "]" :  term
macro_rules
| `([faq_error| $x:term ]) => do 
      Macro.throwError "error!"
      return x

def faq_error_example : Int := [faq_error| 42]
-- error!
