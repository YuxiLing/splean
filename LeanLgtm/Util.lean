import Lean
import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
import Qq

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

register_simp_attr heapSimp

-- partial def getList! (xs : Expr) : MetaM (List Expr) := do
--   match_expr xs with
--   | List.nil _ => return []
--   | List.cons _ x xs => do
--     let xs ← getList! xs
--     return x::xs
--   | _ => throwError "toLeanList: {xs} is not a list"

partial def getList! (xs : Syntax) : (List Syntax) :=
  match xs with
  | `(List.nil) => []
  | `(List.cons $x $xs) => x::getList! xs
  | _ => panic! "getList!: {xs} is not a list"

private def castToProp (e: Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Q(Prop)) := do
  Qq.checkTypeQ (u := Lean.levelOne) e q(Prop)

def getGoalProp : Lean.Elab.Tactic.TacticM Q(Prop) := do
  let goal ← Lean.Elab.Tactic.getMainTarget
  match ← castToProp goal with
  | some qType => return qType
  | none => throwError "goal is not a proposition"


def delabAll :=  (withOptions (fun _ => {}) $ PrettyPrinter.delab ·)

def getGoalStxAll : Lean.Elab.Tactic.TacticM Syntax := do
  delabAll $ <- getMainTarget



-- #eval show MetaM (List Expr) from do
--   let x <- `(term| [true,true,true])
--   let x <- liftCommandElabM $ liftTermElabM $ Term.elabTerm x none
--   toLeanList x
