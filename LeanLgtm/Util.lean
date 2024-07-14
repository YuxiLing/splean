import Lean
import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
import Qq
import SSReflect.Lang

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


def delabAll :=
  (withOptions (fun _ => KVMap.empty.insert `pp.funBinderTypes true) $ PrettyPrinter.delab ·)

def delabPpAll :=
  (withOptions (fun _ => KVMap.empty.insert `pp.all true) $ PrettyPrinter.delab ·)


def delabNoNotations :=
  (withOptions (fun _ =>
    ((KVMap.empty.insert
      `pp.notation false).insert
      `pp.funBinderTypes true).insert
      `pp.explicit true) $ PrettyPrinter.delab ·)

def getGoalStxAll : Lean.Elab.Tactic.TacticM Syntax := do
  delabAll $ <- getMainTarget


initialize
  registerTraceClass `xsimp_step_l
initialize
  registerTraceClass `xsimp_step_r
initialize
  registerTraceClass `xsimp_step_lr
initialize
  registerTraceClass `xsimp


abbrev HintExtState := List Syntax

initialize hintExt : EnvExtension HintExtState ←
  registerEnvExtension (pure [])

syntax "{|" tacticSeq "|}" : term

macro_rules
  | `(term| {| $seq |}) => `(withMainContext do evalTactic $ <- `(tacticSeq| $seq))

partial def repeat'' (tac : TacticM Unit) : TacticM Unit := do
  try
    withMainContext tac
  catch _ => return ()
  repeat'' tac

def _root_.Lean.TSyntax.isMVarStx (x : Term) : Bool :=
  match x with
  | `(?$_) => true
  | _ => false

  syntax "sdo" num tactic : tactic

partial def elabSDo (n : Nat) (tac : Lean.Elab.Tactic.TacticM Unit) : Lean.Elab.Tactic.TacticM Unit := do
  if n == 0 then
    return ()
  else
    tryGoal tac
    allGoal $ elabSDo (n - 1) tac

elab_rules : tactic
  | `(tactic| sdo $n $t) => do
    elabSDo n.getNat (elabTactic t)


-- #eval show MetaM (List Expr) from do
--   let x <- `(term| [true,true,true])
--   let x <- liftCommandElabM $ liftTermElabM $ Term.elabTerm x none
--   toLeanList x
