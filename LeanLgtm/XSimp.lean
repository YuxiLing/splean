import Lean.Elab.Tactic
import Qq

import SSReflect.Lang

import LeanLgtm.Basic
import LeanLgtm.Util


open hprop_scope
open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/-
Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 ->
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.
-/
lemma himpl_of_eq H1 H2 : H1 = H2 -> H1 ==> H2 :=
  by sby move=>-> ?

lemma himpl_of_eq_sym H1 H2  : H1 = H2 -> H2 ==> H1 :=
  by sby move=>-> ?


/-
Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
-/

/- Hack to solve `H ==> H` automatically. What is a better way?  -/
@[simp]
lemma himpl_refl_resolve  H : (H ==> H) = True := by
  sby simp=> ?

lemma himpl_hstar_trans_l H1 H2 H3 H4 :
  H1 ==> H2 ->
  H2 ∗ H3 ==> H4 ->
  H1 ∗ H3 ==> H4 := by
  move=> ??
  eapply himpl_trans=> //
  apply himpl_frame_lr=> //

lemma qimpl_refl (Q : α -> hprop) : Q ===> Q := by
  sby move=> ?; apply himpl_refl

/- Hack to solve `Q ===> Q` automatically. What is a better way?  -/
@[simp]
lemma qimpl_refl_resolve (Q : α -> hprop) : (Q ===> Q) = True := by
  sby simp=> ??

lemma qimpl_trans (Q1 Q2 Q3 : α -> hprop) :
  Q1 ===> Q2 ->
  Q2 ===> Q3 ->
  Q1 ===> Q3 := by
  sby move=> q12 q23 ?? /q12 /q23

lemma qimpl_antisym (Q1 Q2 : α -> hprop) :
  Q1 ===> Q2 ->
  Q2 ===> Q1 ->
  Q1 = Q2 := by
  sby move=> q12 q21;
      apply funext=> ?
      apply himpl_antisym
      { apply q12 }
      apply q21

lemma hstar_comm_assoc (H1 H2 H3 : hprop) :
  H1 ∗ H2 ∗ H3 = H2 ∗ H1 ∗ H3 := by
  sby srw -hstar_assoc [2]hstar_comm hstar_assoc

@[simp]
lemma star_post_empty (Q : α -> hprop) :
  Q ∗∗ emp = Q := by
  move=> !?; srw qstar hstar_hempty_r


attribute [heapSimp] hstar_hempty_l hstar_hempty_r
                     hstar_assoc star_post_empty hwand_hempty_l

macro "hsimp" : tactic => `(tactic| simp only [heapSimp])


def hstarList : List hprop -> hprop
  | [] => emp
  | [h] => h
  | h::hs => h ∗ hstarList hs

def XSimp (hl hr : List hprop × List hprop × List hprop) :=
  let (hla, hlw, hlt) := hl
  let (hra, hrg, hrt) := hr
  hstarList hla ∗ hstarList hlw ∗ hstarList hlt ==>
  hstarList hra ∗ hstarList hrg ∗ hstarList hrt

def protect (x : α) := x

def hstarGetList (hs : Expr) : MetaM $ List Expr :=
  let_expr hstarList hs := hs | throwError "hstarListToList: {hs} is not a hstar of a list"
  getList! hs

structure XSimpR where
  hla : List Expr
  hlw : List Expr
  hlt : List Expr
  hra : List Expr
  hrg : List Expr
  hrt : List Expr


def XSimpRIni : TacticM XSimpR := do
  match <- getGoalProp with
  | ~q(XSimp ($hla, $hlw, $hlt) ($hra, $hrg, $hrt)) =>
    let hla <- hstarGetList hla
    let hlw <- hstarGetList hlw
    let hlt <- hstarGetList hlt
    let hra <- hstarGetList hra
    let hrg <- hstarGetList hrg
    let hrt <- hstarGetList hrt
    return { hla := hla, hlw := hlw, hlt := hlt, hra := hra, hrg := hrg, hrt := hrt }
  | _ => throwError "goal is not a XSimp goal"

def xsimp_step1 (xsr : XSimpR) : XSimpR := sorry

def xsimp_step2 (xsr : XSimpR) : TacticM XSimpR :=
  /- apply lemmas -/
  return xsimp_step1 xsr

/-
approx 1: (Fast)
  xsimp:

  Goal1 ~~> XSimpR

  xsimp_step: XSimpR -> XSimpR

  XSimpR ~~> Goal2 (obligation: Goal2 -> Goal1)
-/

/-
approx 2: (Slow)
  xsimp:

  Goal1 ~~> XSimpR

  xsimp_step: XSimpR -> TacticM XSimpR

  XSimpR ~~> Goal2 (obligation: Goal2 -> Goal1)
-/

/-
approx 3: (Fast->Slow)
  xsimp:

  Goal1 ~~> XSimpR

  xsimp_step: XSimpR -> TacticM XSimpR

  XSimpR ~~> Goal2 (obligation: Goal2 -> Goal1)
-/
