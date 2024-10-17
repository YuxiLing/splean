import Lean.Elab.Tactic

import Lgtm.Common.Util
import Lgtm.Unary.XChange

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- ----------------------------------------------------------------- -/
/-* *** Tactic [ychange] -/

/-* [ychange] performs rewriting on the LHS of an entailment.
  Essentially, it applies to a goal of the form [H1 ∗ H2 ==> H3],
  and exploits an entailment [H1 ==> H1'] to replace the goal with
  [H1' \* H2 ==> H3].

  The tactic is actually a bit more flexible in two respects:
  - it does not force the LHS to be exactly of the form [H1 \* H2]
  - it takes as argument any lemma, whose instantiation result in
    a heap entailment of the form [H1 ==> H1'].

  Concretely, the tactic is just a wrapper around an application
  of the lemma called [ychange_lemma], which appears below.

  [ychanges] combines a call to [ychange] with calls to [xsimpl]
  on the subgoals. -/

lemma ychange_lemma (H1 : hhProp α) :
  H1 ==> H2 ->
  H3 ==> H1 ∗ (H2 -∗ protect H4) ->
  H3 ==> H4 := by sorry

def toHHimp (e : Expr) : MetaM Expr := do
  let eTy <- inferType e
  trace[ychange] "type of give hypothesis {eTy}"
  forallTelescope eTy fun xs eTy => do
    let himpl <- match_expr eTy with
      | hhimpl _ _ _ => return e
      | hqimpl _ _ _ _ => return e
      | Eq _ _ _  =>
        mkAppOptM `hhimpl_of_eq #[.none, .none, eTy]
      | _        => throwError "Expected a heap entailment or an equality"
    mkForallFVars xs himpl

def ychangeApply (l : Expr) : MVarId -> MetaM (List MVarId) := fun goal => do
  let g :: gs <- goal.applyConst `ychange_lemma | throwError "Expected a heap entailment"
  let gs' <- g.apply $ <- toHHimp l
  return gs ++ gs'

def ychangeCore (l : Expr) : MVarId -> MetaM (List MVarId) := fun goal => do
  let goal <-
    match_expr <- goal.getType with
    | hhimpl _ _ _ => pure goal
    | hqimpl _ _ _ _ => pure (<- goal.intro1P).2
    | _ => throwError "Expected a heap entailment"
  ychangeApply l goal

elab "ychange_core" l:term : tactic => withMainContext do
  let (l, mvs) <- Tactic.elabTermWithHoles l none `ychange (allowNaturalHoles := true)
  let gs <- ychangeCore l (<- getMainGoal)
  replaceMainGoal $ gs ++ mvs

macro "ychange" l:term : tactic =>
  `(tactic| (ychange_core $l; ysimp))

macro "ychanges" l:term : tactic =>
  `(tactic| (ychange_core $l; unfold protect; ysimp))

/- ----------------------------------------------------------------- -/
/-* *** [ychange] demos -/

-- set_option trace.ychange true
example (H1 : hhProp α) :
  H1 ==> H2 ∗ H3 ->
  H1 ∗ H4 ==> (H5 -∗ H6) := by
  intro M
  dup 2
  { ychange M; sorry }
  ychanges M; sorry

example (Q : β -> hhProp α) :
  H1 ==> (∃ʰ x, Q x ∗ (H2 -∗ H3)) ->
  H1 ∗ H2 ==> ∃ʰ x, Q x ∗ H3 := by
  intro M
  dup 2
  { ychange M=> x; ysimp }
  ychanges M

-- set_option pp.explicit true
-- set_option pp.notation false

example (Q : Int -> hhProp α) :
  (∀ {β :Type} (x:β) (J:β ->hhProp α), (hhforall J) ==> (J x)) ->
  (h∀ x, Q x) ∗ H ==> Q 2 ∗ (⊤ : hhProp α) := by
  intro M
  ychange M (2 : Int)
  ysimp

-- def xcahngeCore (l : Expr) : TacticM Unit := do
--   let goal <- getMainGoal
--   let goalTy <- getMainTarget
--   let _ <- match_expr goalTy with
--   | himpl _ _ => return ( )
--   | qimpl _ _ _ => goal.intro1P
--   | _ => throwError "Expected a heap entailment"
--     ychangeApply
