import Lean
import Lgtm.Unary.Lang
import Lgtm.Unary.WPUtil
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.WP

open Lean Meta Elab Tactic
open val trm

abbrev YAppExtState := RBMap Name Name Name.cmp

initialize yappExtension :
    SimpleScopedEnvExtension (Name × Name) YAppExtState <-
  registerSimpleScopedEnvExtension {
    name := `yapp
    initial := { }
    addEntry := fun s (n, thm) => s.insert n thm
  }


def getHTripleFun (g : Expr) : MetaM Name := do
  let t <-
    match_expr g with
    | htriple _ _ t _ _ => pure t
    | hhimpl _ _ wp =>
      let_expr hwp _ _ t _ := wp | throwError "hyper implication does not have a wp"
      pure t
    | _ => throwError "goal is not a hyper triple or hyper implication"
  lambdaTelescope t fun _ t => do
    let_expr trm_app t _ := t | throwError "hyper triple term is not an application"
    let .some n := (getNestedApp t).constName? | throwError "nested application in a hyper term is not a constant"
    return n

def pickHTripleLemma : TacticM Name := do
  let n <- getHTripleFun (<- getMainTarget)
  let .some thm := (yappExtension.getState (← getEnv)).find? n | throwError "no triple lemma found"
  return thm



set_option linter.hashCommand false

elab "#hint_yapp" thm:ident : command => do
  Command.runTermElabM fun _ => do
    let thm := (<- Term.elabTerm thm none)
    let .some thmName := thm.getAppFn.constName? | throwError "invalid theorem"
    let thm <- Meta.inferType thm
    let thmFun <- Meta.forallTelescope thm fun _ thm => do
      getHTripleFun thm
    yappExtension.add (thmFun, thmName)

initialize registerBuiltinAttribute {
  name := `yapp
  descr := "Adds a hyper triple lemma to the yapp database"
  add := fun thmName _ _ => do
    MetaM.run' do
      let thm : Expr <- Term.TermElabM.run' <| Term.elabTerm (mkIdent thmName) none
      let thm <- Meta.inferType thm
      let thmFun <- Meta.forallTelescope thm fun _ thm => do
        getHTripleFun thm
      yappExtension.add (thmFun, thmName)
}

register_simp_attr hhlocalE
