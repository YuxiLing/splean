import Lean.Elab.Tactic
import Qq

-- import SSReflect.Lang

import Lgtm.Unary.Util
import Lgtm.Unary.XSimp

import Lgtm.Hyper.HProp


-- open hprop_scope
open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- **============ `hsimp` trivrial goal simplification tactic ============** -/

variable {α : Type}

attribute [-simp] hhwandE

section
local notation "hhProp" => hhProp α
local notation "hheap" => hheap α


lemma hhimpl_of_eq (H1 H2 : hhProp) : H1 = H2 -> H1 ==> H2 :=
  by sby move=>-> ?

/- Hack to solve `H ==> H` automatically. What is a better way?  -/
@[simp]
lemma hhimpl_refl_resolve (H : hhProp) : (H ==> H) = True := by
  sby simp=> ?

-- lemma himpl_hstar_trans_l H1 H2 H3 H4 :
--   H1 ==> H2 ->
--   H2 ∗ H3 ==> H4 ->
--   H1 ∗ H3 ==> H4 := by
--   move=> ??
--   eapply himpl_trans=> //
--   apply himpl_frame_lr=> //

lemma hqimpl_refl (Q : α -> hhProp) : Q ===> Q := by
  sby move=> ?; apply hhimpl_refl

/- Hack to solve `Q ===> Q` automatically. What is a better way?  -/
@[simp]
lemma hqimpl_refl_resolve (Q : α -> hhProp) : (Q ===> Q) = True := by
  sby simp=> ??


lemma hhstar_comm_assoc (H1 H2 H3 : hhProp) :
  H1 ∗ H2 ∗ H3 = H2 ∗ H1 ∗ H3 := by
  sby srw -hhstar_assoc [2]hhstar_comm hhstar_assoc

@[simp]
lemma hstar_post_empty (Q : α -> hhProp) :
  Q ∗ (emp : hhProp) = Q := by
  move=> !?; srw hqstarE hhstar_hhempty_r


attribute [heapSimp] hhstar_hhempty_l hhstar_hhempty_r
                     hhstar_assoc hstar_post_empty hhwand_hempty_l bighstar_hhempty



/- **============ `ysimp` implementation ============** -/

def YSimp (hl hr : hhProp × hhProp × hhProp) :=
  let (hla, hlw, hlt) := hl
  let (hra, hrg, hrt) := hr
  hla ∗ hlw ∗ hlt ==> hra ∗ hrg ∗ hrt

structure YSimpR where
  hla : Term
  hlw : Term
  hlt : Term
  ----------
  hra : Term
  hrg : Term
  hrt : Term

/-
YSimp
      (@Prod.mk hProp (Prod hProp hProp)
        (@HStar.hStar hProp hProp $_ H1 (@HStar.hStar hProp hProp $_ H2 (@HStar.hStar hProp hProp $_ H3 (@HStar.hStar hProp hProp $_ (Q true) (@HStar.hStar hProp hProp $_ (@HWand.hWand hProp hProp $_ (hpure P) HX) (@HStar.hStar hProp hProp $_ HY hempty))))))
        (@Prod.mk hProp hProp Hlw Hlt))
      (@Prod.mk hProp (Prod hProp hProp) Hra (@Prod.mk hProp hProp Hrg Hrt))
-/

def YSimpRIni : TacticM YSimpR := withMainContext do
  (<- getMainGoal).setTag `ysimp_goal
  let goal <- getGoalStxNN
  let `(@YSimp $_ $hl $hr) := goal | throwError "not a YSimp goal"
  let `(@Prod.mk $_ $_ $hla $hlwt) := hl | throwError "not a YSimp goal"
  let `(@Prod.mk $_ $_ $hlw $hlt) := hlwt | throwError "not a YSimp goal"
  let `(@Prod.mk $_ $_ $hra $hrgt) := hr | throwError "not a YSimp goal"
  let `(@Prod.mk $_ $_ $hrg $hrt) := hrgt | throwError "not a YSimp goal"
  return { hla := hla, hlw := hlw, hlt := hlt, hra := hra, hrg := hrg, hrt := hrt }


/- ------------ Tactic for flipping an interated [∗] operation ------------ -/

lemma hhstar_flip_0 :
  (emp : hhProp) = emp := by
  sdone

lemma hhstar_flip_1 :
  h1 ∗ emp = h1 ∗ emp := by
  sdone

lemma hhstar_flip_2 :
  h1 ∗ h2 ∗ emp = h2 ∗ h1 ∗ emp := by
  srw hhstar_comm_assoc

lemma hhstar_flip_3 :
  h1 ∗ h2 ∗ h3 ∗ emp = h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_2 !(hhstar_comm_assoc h3)

lemma hhstar_flip_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ emp = h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_3 !(hhstar_comm_assoc h4)

lemma hhstar_flip_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ emp = h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_4 !(hhstar_comm_assoc h5)

lemma hhstar_flip_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ emp =
  h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_5 !(hhstar_comm_assoc h6)

lemma hhstar_flip_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ emp =
  h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_6 !(hhstar_comm_assoc h7)

lemma hhstar_flip_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ emp =
  h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_7 !(hhstar_comm_assoc h8)

lemma hhstar_flip_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ emp =
  h9 ∗ h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_8 !(hhstar_comm_assoc h9)

lemma hhstar_flip_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 ∗ emp =
  h10 ∗ h9 ∗ h8 ∗ h7 ∗ h6 ∗ h5 ∗ h4 ∗ h3 ∗ h2 ∗ h1 ∗ emp := by
  srw [0] hhstar_flip_9 !(hhstar_comm_assoc h10)

def hhstar_flip_lemma (i : Nat) : Ident :=
  mkIdent s!"hhstar_flip_{i}".toName

partial def hhstar_arity (hs : Term) : TacticM Nat :=
  match hs with
  | `(@hhempty $_)      => return (0)
  | `(@HStar.hStar $_ $_ $_ $_ $_ $h2) => do
      let n <- hhstar_arity h2
      return (1 + n)
  | _           => throwError "cannot get arity"

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

elab "hhstar_flip" h:term : tactic => do
  let i <- hhstar_arity h
  {| eapply $(hhstar_flip_lemma i) |}

lemma ysimp_flip_acc_l_lemma :
  hla = hla' →
  YSimp (hla', emp, emp) (hra, hrg, emp) →
  YSimp (hla, emp, emp) (hra, hrg, emp) := by
  sby move=> h /h

lemma ysimp_flip_acc_r_lemma :
  hra = hra' →
  YSimp (hla, emp, emp) (hra', hrg, emp) →
  YSimp (hla, emp, emp) (hra, hrg, emp) := by
  sby move=> h /h

elab "ysimp_flip_acc_l" hla:term : tactic =>
  {| eapply ysimp_flip_acc_l_lemma ; hhstar_flip $hla |}

elab "ysimp_flip_acc_r" hra:term : tactic =>
  {| eapply ysimp_flip_acc_r_lemma ; hhstar_flip $hra |}

def ysimp_flip_acc_lr (hla hra : Term) : TacticM Unit :=
  {| ysimp_flip_acc_l $hla ; ysimp_flip_acc_r $hra |}


/- ------------ Tactic for picking a particular heap proposition ------------ -/

/- TODO: Pregenerate such lemmas automatically -/
/- Note: Copilot can generate them pretty good -/
lemma hhstar_pick_1 :
  h1 ∗ h = h1 ∗ h := by
  sdone

lemma hhstar_pick_2  :
  h1 ∗ h2 ∗ h = h2 ∗ h1 ∗ h := by
  sby srw hhstar_comm_assoc

lemma hhstar_pick_3 :
  h1 ∗ h2 ∗ h3 ∗ h = h3 ∗ h1 ∗ h2 ∗ h := by
  sby srw (hhstar_comm_assoc h2); apply hhstar_pick_2

lemma hhstar_pick_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h = h4 ∗ h1 ∗ h2 ∗ h3 ∗ h := by
  sby srw (hhstar_comm_assoc h3); apply hhstar_pick_3

lemma hhstar_pick_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h := by
  sby srw (hhstar_comm_assoc h4); apply hhstar_pick_4

lemma hhstar_pick_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h := by
  sby srw (hhstar_comm_assoc h5); apply hhstar_pick_5

lemma hhstar_pick_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h := by
  sby srw (hhstar_comm_assoc h6); apply hhstar_pick_6

lemma hhstar_pick_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h := by
  sby srw (hhstar_comm_assoc h7); apply hhstar_pick_7

lemma hhstar_pick_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h := by
  sby srw (hhstar_comm_assoc h8); apply hhstar_pick_8

lemma hhstar_pick_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 ∗ h = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h := by
  sby srw (hhstar_comm_assoc h9); apply hhstar_pick_9

lemma hhstar_pick_last_1 :
  h1 = h1 := by sdone

lemma hhstar_pick_last_2 :
  h1 ∗ h2 = h2 ∗ h1 := by
  sby srw hhstar_comm

lemma hhstar_pick_last_3 :
  h1 ∗ h2 ∗ h3 = h3 ∗ h1 ∗ h2 := by
  sby srw (@hhstar_comm _ h2); apply hhstar_pick_2

lemma hhstar_pick_last_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 = h4 ∗ h1 ∗ h2 ∗ h3 := by
  sby srw (@hhstar_comm _ h3); apply hhstar_pick_3

lemma hhstar_pick_last_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 := by
  sby srw (@hhstar_comm _ h4); apply hhstar_pick_4

lemma hhstar_pick_last_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 := by
  sby srw (@hhstar_comm _ h5); apply hhstar_pick_5

lemma hhstar_pick_last_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 := by
  sby srw (@hhstar_comm _ h6); apply hhstar_pick_6

lemma hhstar_pick_last_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 := by
  sby srw (@hhstar_comm _ h7); apply hhstar_pick_7

lemma hhstar_pick_last_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 := by
  sby srw (@hhstar_comm _ h8); apply hhstar_pick_8

lemma hhstar_pick_last_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 := by
  sby srw (@hhstar_comm _ h9); apply hhstar_pick_9

def hhstar_pick_lemma (i : Nat) (pickLast : Bool) : Ident :=
  if pickLast then
    mkIdent s!"hhstar_pick_last_{i}".toName
  else
    mkIdent s!"hhstar_pick_{i}".toName

lemma ysimp_pick_lemma :
  hla2 = hla1 ->
  YSimp (hla1, hlw, hlt) hr ->
  YSimp (hla2, hlw, hlt) hr := by sby move=>->

def ysimp_pick (i : Nat) (last? : Bool) : TacticM Unit :=
   {| apply ysimp_pick_lemma
      · apply $(hhstar_pick_lemma i last?) |}

partial def hhstar_search (hs : Term) (test : Nat -> Term -> optParam Bool false -> TacticM Unit) :=
  let rec loop (i : Nat) (hs : Term)  : TacticM Unit := do
    match hs with
    | `(@HStar.hStar $_ $_ $_ $_ $h1 $h2) => do
      try
        test i h1
      catch _ => loop (i+1) h2
    | _ => test i hs true
  loop 1 hs

def ysimp_pick_same (h hla : Term) (f : optParam (Nat → Bool → TacticM Unit) ysimp_pick) : TacticM Unit := do
  let h  <- Tactic.elabTerm h none
  hhstar_search hla fun i h' last? => do
    let h' <- Tactic.elabTerm h' none
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h' h | throwError "not equal"
    f i last?

def ysimp_pick_applied (h hla : Term) : TacticM Unit := do
  let h <- Term.elabTerm h  none
  hhstar_search hla fun i h' last? => do
    let h' <- Term.elabTerm h' none
    let numArgs + 1 := h'.getAppNumArgs' | throwError "not equal"
    let h' := h'.consumeMData.getAppPrefix numArgs
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h h' | throwError "not equal"
    ysimp_pick i last?


/- ============ Theory for `ysimp` ============ -/
lemma ysimp_start_lemma :
  YSimp (emp, emp, h1 ∗ emp) (emp, emp, h2 ∗ emp) ->
  h1 ==> h2 := by
  sby srw YSimp ; hsimp

/- ----- Cancellation tactic for proving [ysimp] lemmas ----- -/

lemma hhstar_simp_start_lemma :
  H1 ∗ emp ==> emp ∗ H2 ∗ emp →
  H1 ==> H2 := by
  sby hsimp

lemma hhstar_simp_keep_lemma :
  H1 ==> (H ∗ Ha) ∗ Ht →
  H1 ==> Ha ∗ H ∗ Ht := by
  sby hsimp ; srw hhstar_comm_assoc

lemma hhstar_simp_cancel_lemma :
  H1 ==> Ha ∗ Ht →
  H ∗ H1 ==> Ha ∗ H ∗ Ht := by
  srw hhstar_comm_assoc=> ?
  sby apply hhimpl_frame_lr

lemma hhstar_simp_pick_lemma :
  H1 = H1' →
  H1' ==> H2 →
  H1 ==> H2 := by
  sby move=> h /h

def hhstar_simp_pick (i : Nat) (_ : Bool) : TacticM Unit :=
  let L := hhstar_pick_lemma i false
  {| eapply hhstar_simp_pick_lemma ; apply $(L) |}

def hhstar_simp_start : TacticM Unit := withMainContext do
  let goal <- getGoalStxNN
  match goal with
  | `(@hhimpl $_ $_ $_) =>
      {| apply hhstar_simp_start_lemma ; try srw ?hhstar_assoc |}
  | _          => throwError "hhstar_simp_start failure"

def hhstar_simp_step : TacticM Unit := withMainContext do
  let goal <- getGoalStxNN
  match goal with
    | `(@hhimpl $_ $Hl $Hr) =>
        match Hr with
          | `(@HStar.hStar $_ $_ $_ $_ $_ $hs) =>
              match hs with
              | `(@HStar.hStar $_ $_ $_ $_ $H $_) =>
                    try
                      ysimp_pick_same H Hl hhstar_simp_pick ;
                      {| apply hhstar_simp_cancel_lemma |}
                    catch ex =>
                      let s <- ex.toMessageData.toString
                      if s == "not equal" then
                        {| apply hhstar_simp_keep_lemma |}
                      else
                        throw ex
              | _ => throwError "cannot simplify"
          | _ => throwError "cannot simplify"
    | _ => throwError "cannot simplify"

def hhstar_simp_post :=
  {| hsimp ; try apply hhimpl_refl |}

elab "hhstar_simp_start" : tactic => do
  hhstar_simp_start

elab "hhstar_simp_step" : tactic => do
  hhstar_simp_step

elab "hhstar_simp" : tactic => do
  hhstar_simp_start ;
  {| repeat hhstar_simp_step |} ;
  hhstar_simp_post


/- ------------ Lemmas for LHS step ------------ -/

macro "ysimp_l_start" : tactic =>
  `(tactic| (srw ?YSimp=> ? ; try hsimp))

macro "ysimp_l_start'" : tactic =>
  `(tactic| (ysimp_l_start ; apply hhimpl_trans; try rotate_left=> //; hhstar_simp ; try hhstar_simp))

lemma ysimp_l_hempty :
  YSimp (hla, hlw, hlt) hr ->
  YSimp (hla, hlw, emp ∗ hlt) hr := by
  sby hsimp

lemma ysimp_l_hpure :
  (p -> YSimp (hla, hlw, hlt) hr) ->
  YSimp (hla, hlw, ⌜p⌝ ∗ hlt) hr := by
  ysimp_l_start
  rw [hhstar_pick_3]
  sby apply hhimpl_hstar_hhpure_l

@[simp]
lemma foo''' : (H ==> H) = true := by
  sby simp

lemma ysimp_l_acc_wand :
  YSimp (hla, h ∗ hlw, hlt) hr ->
  YSimp (hla, hlw, h ∗ hlt) hr := by
  ysimp_l_start'



lemma ysimp_l_acc_other :
  YSimp (h ∗ hla, hlw, hlt) hr ->
  YSimp (hla, hlw, h ∗ hlt) hr := by
  ysimp_l_start'

lemma ysimp_l_hexists.{u} {β : Sort u} {j : β -> _} :
  (∀ x, YSimp (hla, hlw, j x ∗ hlt) hr) ->
  YSimp (hla, hlw, (hhexists j) ∗ hlt) hr := by
  srw ?YSimp=> H
  rw [hhstar_pick_3, hhstar_hhexists_l]
  apply (@hhimpl_hhexists_l _ β (hr.1 ∗ hr.2.1 ∗ hr.2.2) (fun x : β => j x ∗ hla ∗ hlw ∗ hlt))=> x
  rw [<- hhstar_pick_3]
  apply H

lemma ysimp_l_cancel_hwand_hempty :
  YSimp (hla, hlw, h ∗ hlt) hr ->
  YSimp (hla, (emp -∗ h) ∗ hlw, hlt) hr := by

  ysimp_l_start'

lemma ysimpl_l_cancel_hwand_hstar_hempty :
  YSimp (Hla, Hlw, ((H2 -∗ H3) ∗ Hlt)) HR ->
  YSimp (Hla, (((emp ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR := by
  ysimp_l_start'

lemma ysimp_l_keep_wand :
  YSimp (H ∗ Hla, Hlw, Hlt) HR →
  YSimp (Hla, H ∗ Hlw, Hlt) HR := by
  ysimp_l_start'

lemma ysimp_l_hwand_reorder :
  h1 = h1' ->
  YSimp (hla, ((h1' -∗ h2) ∗ hlw), hlt) hr ->
  YSimp (hla, (h1 -∗ h2) ∗ hlw, hlt) hr := by
  sby move=> H /H

/-
  YSimp (hla, (h1 ∗ h2 ∗ ... ∗ hn -∗ h) ∗ hlw, hlt) hr
-/

lemma ysimp_l_cancel_hwand_hstar :
  YSimp (Hla, Hlw, (H2 -∗ H3) ∗ Hlt) HR →
  YSimp ((H1 ∗ Hla), (((H1 ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR := by
  ysimp_l_start'
  srw hhwand_curry_eq
  apply hhwand_cancel

lemma ysimp_l_cancel_hwand :
  YSimp (emp, Hlw, Hla ∗ H2 ∗ Hlt) HR →
  YSimp ((H1 ∗ Hla), ((H1 -∗ H2) ∗ Hlw), Hlt) HR := by
  ysimp_l_start'
  apply hhwand_cancel

lemma ysimp_l_cancel_qwand β (Q1 Q2 : β -> hhProp) x :
  YSimp (emp, Hlw, (Hla ∗ Q2 x ∗ Hlt)) HR ->
  YSimp ((Q1 x ∗ Hla), ((Q1 -∗ Q2) ∗ Hlw), Hlt) HR := by
  ysimp_l_start'
  srw hhstar_comm
  apply (@hhimpl_hhstar_trans_l) ; apply (hqwand_specialize _ x)
  srw hhstar_comm ; apply hhwand_cancel

lemma ypull_protect (h : H1 ==> protect H2) : H1 ==> H2 :=
  by simp [protect] at h; assumption

/- ------------ Lemmas for RHS step ------------ -/

lemma ysimp_r_hempty :
  YSimp hl (hra, hrg, hrt) ->
  YSimp hl (hra, hrg, emp ∗ hrt) := by
  sby srw hhstar_hhempty_l

lemma ysimp_r_hwand_same :
  YSimp hl (hra, hrg, hrt) ->
  YSimp hl (hra, hrg, (h -∗ h) ∗ hrt) := by
  ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp
  sby srw hhwand_equiv ; hsimp

lemma ysimp_r_hpure :
  YSimp hl (hra, hrg, hrt) -> p ->
  YSimp hl (hra, hrg, hhpure p ∗ hrt) := by
  move=> ? ; ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp
  sby apply hhimpl_hempty_hhpure

lemma ysimp_r_hexists.{u} (β : Sort u) (x : β) hl (hra : hhProp) hrg hrt (j : β -> _) :
  YSimp hl (hra, hrg, j x ∗ hrt) ->
  YSimp hl (hra, hrg, (hhexists j) ∗ hrt) := by
  move=> ? ; ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp
  apply hhimpl_hhexists_r
  sdone

lemma ysimp_r_keep :
  YSimp hl (h ∗ hra, hrg, hrt) ->
  YSimp hl (hra, hrg, h ∗ hrt) := by
  move=> ? ; ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp

lemma ysimpl_r_hgc_or_htop :
  YSimp HL (Hra, (H ∗ Hrg), Hrt) ->
  YSimp HL (Hra, Hrg, (H ∗ Hrt)) := by
  move=> ? ; ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp

lemma ysimpl_r_htop_drop :
  YSimp HL (Hra, Hrg, Hrt) ->
  YSimp HL (Hra, Hrg, ((⊤ : hhProp) ∗ Hrt)) := by
  move=> ? ; ysimp_l_start ; apply hhimpl_trans=> //; hhstar_simp ; try hhstar_simp
  apply hhimpl_hhtop_r

/- ------------ Lemmas for LHS/RHS step ------------ -/

macro "ysimp_lr_start" : tactic =>
  `(tactic| (srw ?YSimp ; try hsimp))

macro "ysimp_lr_start'" : tactic =>
  `(tactic| (ysimp_l_start ; try hsimp ; try (apply himp_trans=>// ; hhstar_simp)))

macro "ysimp_lr_start''" : tactic =>
  `(tactic| (ysimp_l_start ; try hsimp ; try (apply himp_trans; rotate_left=>// ; hhstar_simp)))


lemma ysimp_lr_hwand_hfalse :
  YSimp (Hla, emp, emp) ((⌜False⌝ -∗ H1) ∗ emp, emp, emp) := by
  ysimp_lr_start
  srw hhwand_equiv
  sby apply hhimpl_hstar_hhpure_l

lemma ysimp_lr_cancel_same :
  YSimp (hla, hlw, hlt) (hra, hrg, hrt) ->
  YSimp (h ∗ hla, hlw, hlt) (hra, hrg, h ∗ hrt) := by
  ysimp_lr_start'
  srw [2]hhstar_pick_3
  sby apply hhimpl_frame_r

lemma hhimpl_lr_refl :
  YSimp (hla, emp, emp) (hla, emp, emp) := by
  ysimp_l_start'=> //

lemma ysimp_lr_hwand :
  YSimp (emp, emp, (H1 ∗ Hla)) (emp, emp, H2 ∗ emp) ->
  YSimp (Hla, emp, emp) ((H1 -∗ H2) ∗ emp, emp, emp) := by
  srw ?YSimp ; hsimp
  sby srw hhwand_equiv

lemma ysimpl_lr_qwand β (Q1 Q2 : β -> hhProp) :
  (forall x, YSimp (emp, emp, (Q1 x ∗ Hla)) (emp, emp, (Q2 x ∗ emp))) ->
  YSimp (Hla, emp, emp) (((Q1 -∗ Q2) ∗ emp), emp, emp) := by
  ysimp_lr_start
  srw hqwand_equiv=> ??
  srw hqstarE
  sdone

lemma ysimpl_lr_qwand_unit (Q1 Q2 : Unit -> hhProp) :
  YSimp (emp, emp, (Q1 ( ) ∗ Hla)) (emp, emp, (Q2 ( ) ∗ emp)) ->
  YSimp (Hla, emp, emp) ((Q1 -∗ Q2) ∗ emp, emp, emp) := by
  move=> ?
  sby apply ysimpl_lr_qwand=> ?

lemma hhimpl_lr_qwand_unify (Hla : hhProp) (Q : β -> hhProp):
  YSimp (Hla, emp, emp) ((Q -∗ (Q ∗ Hla)) ∗ emp, emp, emp) := by
  srw ?YSimp ; hsimp
  sby srw hqwand_equiv

lemma hhimpl_lr_htop :
  YSimp (emp, emp, emp) (emp, Hrg, emp) ->
  YSimp (Hla, emp, emp) (emp, ((⊤ : hhProp) ∗ Hrg), emp) := by
  ysimp_lr_start=>?
  srw -(@hhstar_hhempty_l _ Hla)
  apply hhimpl_hhstar_trans_l=>// ; hhstar_simp
  apply hhimpl_hhtop_r

lemma ysimpl_lr_hforall (β : Type) (J : β -> hhProp) :
  (forall x, YSimp (emp, emp, Hla) (emp, emp, J x ∗ emp)) ->
  YSimp (Hla, emp, emp) ((hhforall J) ∗ emp, emp, emp) := by
  ysimp_lr_start=>?
  apply hhimpl_hhforall_r=> ?
  sdone

lemma ysimpl_lr_cancel_htop :
  YSimp (Hla, Hlw, Hlt) (Hra, ((⊤ : hhProp) ∗ Hrg), Hrt) ->
  YSimp ((H ∗ Hla), Hlw, Hlt) (Hra, ((⊤ : hhProp) ∗ Hrg), Hrt) := by
  ysimp_lr_start
  srw (hhstar_comm_assoc Hra) -[2]hhstar_hhtop_hhtop ; hsimp=>?
  apply hhimpl_frame_lr=>//

lemma bighsingle_eq {hv₁ hv₂ : α -> val} {p : α -> loc} :
  (∀ a ∈ s, hv₁ a = hv₂ a) ->
  [∗ i in s| p i ~~> hv₁ i] = [∗ i in s| p i ~~> hv₂ i] := by
    sby move=> hveq; apply bighstar_eq=> ? /hveq

lemma ysimpl_lr_cancel_same_hsingle (p : α -> loc) (v1 v2 : α -> val) :
  YSimp (Hla, Hlw, Hlt) (Hra, Hrg, Hrt) →
  (∀ i ∈ s, v1 i = v2 i) →
  YSimp ([∗ i in s | p i ~~> v1 i] ∗ Hla, Hlw, Hlt) (Hra, Hrg, [∗ i in s | p i ~~> v2 i] ∗ Hrt) := by
  move=> ? hveq; srw (bighsingle_eq hveq)
  ysimp_lr_start
  hhstar_simp
  sby srw (@hhstar_comm _ Hrt) (@hhstar_comm _ Hrg) ; hsimp

lemma ysimp_lr_exit :
  Hla ==> Hra ∗ Hrg ->
  YSimp (Hla, emp, emp) (Hra, Hrg, emp) := by
  sby srw ?YSimp ; hsimp

lemma hqstar_simp (Q1 : β -> hhProp) :
  (Q1 ∗ H) x = Q1 x ∗ H := by rfl


/- ----- Tactic for cancelling [hsingle] assertions ----- -/

def ysimp_pick_same_pointer (p hla : Term) : TacticM Unit := withMainContext do
  let p  <- Tactic.elabTerm p none
  hhstar_search hla fun i h' last? => do
    match h' with
      | `(@hhsingle $_ $_ $p' $_) =>
        if p'.isMVarStx then throwError "not equal" else
        let p' <- Tactic.elabTerm p' none
        let .true <-
          withAssignableSyntheticOpaque <| isDefEq p' p | throwError "not equal"
      | _ => throwError "not equal"
    ysimp_pick i last?

lemma hval_int_congr (s : Set α) (n1 n2 : α -> Int) :
  (∀ i ∈ s, n1 i = n2 i) →
  (∀ i ∈ s, val.val_int (n1 i) = val.val_int (n2 i)) := by
  sdone

lemma hval_loc_congr (n1 n2 : α -> loc) (s : Set α) :
  (∀ i ∈ s, n1 i = n2 i) →
  (∀ i ∈ s, val.val_loc (n1 i) = val.val_loc (n2 i)) := by
  sdone
end

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/- TODO: Extend this with some equality over values -/
elab "ysimp_hsingle_discharge" : tactic =>
  withAssignableSyntheticOpaque {|
    -- try congruence lemma
    (try apply hval_int_congr
     try apply hval_loc_congr
     try move=> ??; rfl
     try sdone) |}


/- ============ LHS ysimp step ============ -/

def ysimp_hwand_hstars_l (hla hs : Term) :=
  hhstar_search hs fun i h last? => do
    -- let hhstar_pick := hhstar_pick_lemma i last?
    {| apply ysimp_l_hwand_reorder
       · apply $(hhstar_pick_lemma i last?) |}
    match h with
    | `(@hhempty _) => {| apply ysimpl_l_cancel_hwand_hstar_hempty |}
    | _ => ysimp_pick_same h hla; {| apply ysimp_l_cancel_hwand_hstar |}

def ysimp_apply_intro_names (lem : Name) (xs : Syntax) : TacticM Unit :=
  let lem := mkIdent lem
  match xs with
  | `(Lean.explicitBinders| $xs:unbracketedExplicitBinders) =>
    match xs with
    | `(unbracketedExplicitBinders| $[$xs]* : $_)
    | `(unbracketedExplicitBinders| $[$xs]*) =>
      for x in xs do
        match x with
        | `(binderIdent| $x:ident) =>
          {| apply $lem; intro $x:ident |}
        | `(binderIdent| $_:hole) =>
          {| apply $lem; unhygienic intro |}
        | _ => throwError "ysimp_l_exists: @ unreachable 2"
    | _ => throwError "ysimp_l_exists: @ unreachable 3"
  | `(Lean.explicitBinders| $[$xs]*) =>
      for x in xs do
        match x with
        | `(Lean.bracketedExplicitBinders| ($x:ident : $_) ) =>
          {| apply $lem; intro $x:ident |}
        | _ => throwError "ysimp_l_exists: @ unreachable 1"
  | _ => throwError "ysimp_l_exists: @ unreachable 3"

macro "simpNums" : tactic =>
  `(tactic| (try simp only [foo, foo', foo''] at *; try dsimp at *))

partial def ysimp_step_l (ysimp : YSimpR) (cancelWand := true) : TacticM Unit := do
  trace[ysimp] "LHS step"
  match ysimp.hlt, ysimp.hlw with
  | `(@HStar.hStar $_ $_ $_ $_ $h $_), _ =>
    match h with
    | `(@hhempty $_)         => {| apply ysimp_l_hempty |}
    | `(@hhpure $_ $_)        =>
      let n <- fresh `n
      revExt.modify (n :: ·)
      {| apply ysimp_l_hpure; intro $n:ident |}
    | `(@HStar.hStar $_ $_ $_ $_ $h1 $h2)   =>
      withAssignableSyntheticOpaque {| erw [@hhstar_assoc _ $h1 $h2]; simpNums |}
      -- rewriteTarget (<- `(@hstar_assoc $h1 $h2)) false
      /- we know that here should be another LHS step -/
      ysimp_step_l (<- YSimpRIni) cancelWand
    | `(@hhexists $_ $_ fun ($x:ident : $_) => $_) =>
      revExt.modify (x :: ·)
      {| apply ysimp_l_hexists; intro $x:term |}
    | `(@HWand.hWand $_    $_    $_ $_ $_ $_)   => {| apply ysimp_l_acc_wand |}
    | _              => {| apply ysimp_l_acc_other |}
  | `(@hhempty $_), `(@HStar.hStar $_ $_ $_ $_ $h1 $_) =>
    match h1 with
    | `(@HWand.hWand $tp1 $tp2 $_ $_ $h1 $_) =>
      match tp1, tp2 with
      | `(hhProp $_), `(hhProp $_) =>
        match h1 with
        | `(@hhempty _) => {| apply ysimp_l_cancel_hwand_hempty |}
        | `(@HStar.hStar $_ $_ $_ $_ $_ $_) => ysimp_hwand_hstars_l ysimp.hla h1
        | _ => try
            let .true := cancelWand | failure
            ysimp_pick_same h1 ysimp.hla
            {| apply ysimp_l_cancel_hwand |}
          catch _ => {| apply ysimp_l_keep_wand |}
      | _ , _ =>
        try
          let .true := cancelWand | failure
          ysimp_pick_applied h1 ysimp.hla
          {| apply ysimp_l_cancel_qwand |}
        catch _ => {| apply ysimp_l_keep_wand |}
    | _ => throwError "ysimp_step_l: @ unreachable"
  | _, _ => throwError "ysimp_step_l: @ unreachable"

/- ============ RHS ysimp step ============ -/
-- declare_syntax_cat hint

-- syntax term : hint
-- syntax "?" : hint

-- declare_syntax_cat hints
-- syntax "[" (ppSpace colGt hint),* "]" : hints

-- def eApplyAndName (lem : Name) (mvarName : Name) : TacticM Unit := withMainContext do
--     let g <- getMainGoal
--     let [g, ex] <- g.applyConst lem | throwError "eApplyAndName: should be two goals"
--     let nm <- fresh mvarName
--     ex.setTag nm.getId
--     ex.setUserName nm.getId
--     setGoals [g]


def ysimp_r_hexists_apply_hints (x : Ident) : TacticM Unit := do
  let hints <- hintExt.get
  match hints with
  | [] => eApplyAndName `ysimp_r_hexists $ `ysimp ++ x.getId
  | h :: hs =>
    hintExt.set hs
    match h with
    | `(hint| ?)       => eApplyAndName `ysimp_r_hexists $ `ysimp ++ x.getId
    | `(hint| $t:term) => {| apply (@ysimp_r_hexists _ _ $t) |}
    | _ => throwError "ysimp_r_hexists_apply_hints: @ unreachable"

partial def ysimp_step_r (ysimp : YSimpR) : TacticM Unit := do
  trace[ysimp] "RHS step"
  trace[ysimp] "hrt: {ysimp.hrt}"
  match ysimp.hlw, ysimp.hlt, ysimp.hrt with
  | `(@hhempty $_), `(@hhempty $_), `(@HStar.hStar $_ $_ $_ $_ $h $_) =>
    /- TODO: implement hook -/
    try
      trace[ysimp] "ysimp_r deals with: {h}"
      match h with
      | `(@hhempty $_) => {| apply ysimp_r_hempty |}
      | `(@hhpure $_ $_) => {| apply ysimp_r_hpure |}
      | `(@HStar.hStar $_ $_ $_ $_ $h1 $h2) =>
        {| erw [@hhstar_assoc _ $h1 $h2];
           simpNums |} -- HACK: Numbers are printed with explicict coercions in the goal.
                       -- Somehow rewite adds them as well. So we need to remove them
         /- we know that here should be another RHS step -/
        ysimp_step_r (<- YSimpRIni)
      | `(@HWand.hWand $_ $_ $_ $_ $h1 $_) =>
        match h1 with
        | `(@hhpure $_ $_) => {| apply ysimp_r_keep |}
        | _ => {| apply ysimp_r_hwand_same |}
      | `(@hhtop $_) =>
        match ysimp.hrg with
        | `(@hhempty $_) =>
          {| apply ysimpl_r_hgc_or_htop |}
          repeat'' do
            ysimp_pick_same h ysimp.hla
            {| apply ysimp_lr_cancel_same |}
        | `(@HStar.hStar $_ $_ $_ $_ $hhtop $hhempty) =>
          match hhtop, hhempty with
          | `(@hhtop $_), `(@hhempty $_) => {| apply ysimp_r_htop_drop |}
          | _, _ => throwError "ysimp_step_r: @ unreachable"
           {| apply ysimpl_r_htop_drop |}
        | _ => throwError "ysimp_step_r: @ unreachable"
      | `(@hhexists $_ $_ fun ($x:ident : $_) => $_) => ysimp_r_hexists_apply_hints x
      | `(protect $_) => {| apply ysimp_r_keep |}
      | `(@hhsingle $_ $_ $x $_) =>
        -- dbg_trace "here: {x}"
        if x.isMVarStx then
          {| apply ysimp_r_keep |}
        else
          ysimp_pick_same_pointer x ysimp.hla
          -- let g <- getMainTarget
          -- trace[ysimp] g
          {| apply ysimpl_lr_cancel_same_hsingle <;>
             ysimp_hsingle_discharge |}
      | _ =>
        if h.isMVarStx then
          {| apply ysimp_r_keep |}
        else
        ysimp_pick_same h ysimp.hla
        {| apply ysimp_lr_cancel_same |}
    catch ex =>
      trace[ysimp] ex.toMessageData
      {| apply ysimp_r_keep |}
  | _, _, _ => throwError "not implemented"

/- ============ LHS/RHS ysimp step ============ -/

def ysimp_step_lr (ysimp : YSimpR) : TacticM Unit := do
  trace[ysimp] "LHS/RHS step"
  match ysimp.hrg with
  | `(@hhempty $_) =>
    trace[ysimp] "here";
    match ysimp.hra with
    | `(@HStar.hStar $_ $_ $_ $_ $h1 $hhempty) =>
      match hhempty with
      | `(@hhempty $_) => {
        if h1.isMVarStx then
          withAssignableSyntheticOpaque {| hsimp; apply hhimpl_lr_refl |}
          return ( );
       match h1 with
       | `(@HWand.hWand $tp1 $tp2 $_ $_ $h1 $_) => do
          match tp1, tp2 with
          | `(hhProp $_), `(hhProp $_) =>
            match h1 with
            | `(@hhpure $_ False) => {| apply ysimp_lr_hwand_hfalse |}
            | _ => /- TODO: flip -/ ysimp_flip_acc_lr ysimp.hla ysimp.hra; {| apply ysimp_lr_hwand |}
          | _, _ =>
            ysimp_flip_acc_lr ysimp.hla ysimp.hra ;
            try
              let .true := h1.isMVarStx | failure
              {| apply hhimpl_lr_qwand_unify |}
            catch _ =>
              {| first | apply ysimpl_lr_qwand_unit
                       | apply ysimpl_lr_qwand; unhygienic intro
                 try simp only [hqstar_simp] |}
        | `(@hhforall $_ $_ fun ($x : $_) => $_) => /- TODO: flip -/
          {| ysimp_flip_acc_l $ysimp.hla ; apply ysimpl_lr_hforall; intro $x:term |}
        | _ => do /- TODO: flip -/ ysimp_flip_acc_lr ysimp.hla ysimp.hra ; {| apply ysimp_lr_exit |} }
      | _ => ysimp_flip_acc_lr ysimp.hla ysimp.hra ; {| apply ysimp_lr_exit |}
    | `(@hhempty $_) => {| first | apply hhimpl_lr_refl | apply ysimp_lr_exit |}
    | _ => /- TODO: flip -/ ysimp_flip_acc_lr ysimp.hla ysimp.hra ; {| apply ysimp_lr_exit |}
  | `(@HStar.hStar $_ $_ $_ $_ $hhtop $hhempty) =>
    match hhtop, hhempty with
    | `(@hhtop $_), `(@hhempty $_) => {| first | apply hhimpl_lr_htop | apply ysimp_lr_exit |}
    | _, _ => ysimp_flip_acc_lr ysimp.hla ysimp.hra ; {| apply ysimp_lr_exit |}
  | _ => /- TODO: flip -/ ysimp_flip_acc_lr ysimp.hla ysimp.hra ; {| apply ysimp_lr_exit |}


/- ============ Tactic Notations ============ -/

elab "ysimp_step" : tactic => do
  let ysimp <- YSimpRIni
  /- TODO: optimise.
    Sometimes we tell that some transitions are not availible at the moment.
    So it might be possible to come up with something better than trying all
    transitions one by one -/
  withMainContext do
    ysimp_step_l  ysimp <|>
    ysimp_step_r  ysimp <|>
    ysimp_step_lr ysimp

elab "rev_pure" : tactic => do
  {| try subst_vars |}
  for n in <- revExt.get do
    withMainContext do
    {| try  revert $n:ident |}
  revExt.set []


elab "ysimp_handle_qimpl" : tactic => do
  match_expr <- getMainTarget with
  | hqimpl _ tp _ q2 =>
    if q2.isMVar then
      {| apply hqimpl_refl |}
    else if tp.isConstOf `Unit then
      {| scase |}
    else let r <- fresh `r; {| intros $r |}
  | hhimpl _ _ h2 =>
     if h2.isMVar then
      {| apply hhimpl_refl |}
     else return ( )
  | Eq tp _ _ =>
    let_expr hhProp _ := tp | throwError "not a goal for ysimp/ypull"
    {| apply hhimpl_antisymm |}
  | Eq tp _ _ =>
    let .some (_, tp) := tp.arrow? | throwError "not a goal for ysimp/ypull"
    let_expr hhProp _ := tp | throwError "not a goal for ysimp/ypull"
    {| ext; apply hhimpl_antisymm |}
  | _ => throwError "not a goal for ysimp/ypull"

macro "ypull_start" : tactic =>
  `(tactic|
     (ysimp_handle_qimpl
      apply ypull_protect
      apply ysimp_start_lemma
      try simp only [hqstarE]))

macro "ysimp_start" : tactic =>
  `(tactic|
    (ysimp_handle_qimpl
     try apply ysimp_start_lemma
     try simp only [hqstarE]))

macro "ypull" : tactic =>
  `(tactic| (
    ypull_start
    repeat' ysimp_step
    try rev_pure
    hsimp
  ))

elab "hide_mvars" : tactic => do
  let gs <- getUnsolvedGoals
  let mut gs' := []
  for g in gs do
    let tp <- Meta.inferType (<- g.getType)
    if tp.isProp then
      gs' := g :: gs'
  setGoals gs'.reverse


macro "ysimp" : tactic =>
  `(tactic| (
    ysimp_start
    repeat ysimp_step
    try rev_pure
    try hide_mvars
    try hsimp
    rotate_left

  ))

elab "ysimp" ls:hints : tactic => do
  match ls with
  | `(hints| [ $[$hs],* ]) =>
    hintExt.set hs.toList
    {| ysimp_start
       repeat ysimp_step
       try rev_pure
       try hsimp
       rotate_left
        |}
  | _ => throwError "ysimp: unreachable"

/- **============ Test Cases ============** -/
section

-- lemma dup_lemma (p : Prop) : p -> p -> p := by sdone

-- partial def dup (n : Nat) : TacticM Unit := do
--   match n with
--   | 0 => {|skip|}
--   | _ => dup (n-1); {| apply dup_lemma|}

elab "dup" n:num : tactic =>
  dup $ n.getNat -1

/- [hhstar_pick] -/
section

local elab "pick" i:num : tactic =>
  let l := hhstar_pick_lemma i.getNat false
  {|apply $l|}

local elab "pickl" i:num : tactic =>
  let l := hhstar_pick_lemma i.getNat true
  {|apply $l|}

example :
  (forall H, H1 ∗ H2 ∗ H3 ∗ H4 = H -> H = Hresult -> True) -> True := by
  intro M
  dup 2 <;> eapply M
  { pick 3 }
  { admit }
  { pickl 4 }
  { admit }

/- `ysimp_pick` -/

local elab "ysimp_pick" i:num : tactic =>
  ysimp_pick i.getNat false

local elab "ysimp_pickl" i:num : tactic =>
  ysimp_pick i.getNat true

local elab "ysimp_pick_same" h:term : tactic => do
  let ysimp <- YSimpRIni
  ysimp_pick_same h ysimp.hla

local elab "ysimp_pick_applied" h:term : tactic => do
  let ysimp <- YSimpRIni
  ysimp_pick_applied h ysimp.hla

-- set_option pp.all true
example (Q : Bool -> _):
  (forall HX HY,
    YSimp ((H1 ∗ H2 ∗ H3 ∗ Q true ∗ (⌜P⌝ -∗ HX) ∗ HY ∗ emp), Hlw, Hlt)
           (Hra, Hrg, Hrt)
  -> True) -> True := by
  move=> M
  eapply M
  ysimp_pick 2
  ysimp_pick_same H3
  ysimp_pick_applied Q
  ysimp_pick_same H2
  ysimp_pick_same H3
  ysimp_pick_same ⌜True⌝
  ysimp_pick_same (⌜P⌝ -∗ H1)
  admit

/- `ysimp/ypull` -/

local macro "ypull0" : tactic => `(tactic| ypull_start)
local macro "ysimp0" : tactic => `(tactic| ysimp_start)
local macro "ysimp1" : tactic => `(tactic| ysimp_step)
local elab "ysimpl" : tactic => do
  ysimp_step_l (<- YSimpRIni) true
local elab "ysimpr" : tactic => do
  ysimp_step_r (<- YSimpRIni)

example :
  (H1 ∗ emp ∗ (H2 ∗ (∃ʰ (y:Int) (z : Int) (n:Int), ⌜y = y + z + n⌝)) ∗ H3) ==> H :=
  by
    dup 2
    { ypull0; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1;
      admit }
    { ypull; admit }

-- set_option trace.ysimp true
example (α : Type) (H1 H2 H3 H4 H5 : hhProp α) :
  H1 ∗ H2 ∗ H3 ∗ H4 ==> H4 ∗ H3 ∗ H5 ∗ H2 :=
  by
    dup 3
    { ypull; admit }
    { ysimp0
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      ysimp1
      admit }
    ysimp; admit

/--
warning: declaration uses 'sorry'
---
info: case ysimp_goal.a.a.a
α α✝ : Type
H1 H2 H3 H4 H5 H6 H7 : hhProp α✝
⊢ H1 ∗ H2 ∗ H4 ==> H5 ∗ H6 ∗ H7
-/
#guard_msgs in
example :
  H1 ∗ H2 ∗ H3 ∗ H4 ==> H5 ∗ H3 ∗ H6 ∗ H7 := by
  ysimp
  trace_state
  admit

example (α : Type) (H1 H2 H3 H4 H5 : hhProp α) :
  H1 ∗ H2 ∗ H3 ∗ H4 ∗ H5 ==> H3 ∗ H1 ∗ H2 ∗ (⊤ : hhProp α) := by
  ysimp

example (Q : Int -> _) :
  Q 4 ==> Q 3 ->
  H1 ∗ Q 4 ==> ∃ʰ x, Q x ∗ H1 :=
  by intro; ysimp[3]=> // /- TODO: handle hints -/

example :
  (forall H, H1 ∗ H2 ==> H -> True) -> True :=
  by sapply; ysimp

example :
  (forall H, H1 ==> H1 ∗ H -> True) -> True :=
  by sapply; ysimp

example :
  H1 ∗ H2 ∗ (⊤ : hhProp α) ==> H1 ∗ (⊤ : hhProp α) :=
  by ysimp

example :
  H1 ∗ H2 ∗ (⊤ : hhProp α) ==> H1 ∗ (⊤ : hhProp α) ∗ (⊤ : hhProp α) :=
  by ysimp

example :
  (H1 -∗ (H2 -∗ H3)) ∗ H1 ∗ H4 ==> (H2 -∗ (H3 ∗ H4)) :=
  by
    dup 2
    { ysimp0;
      ysimp1; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1;
      ysimp1; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1;
      ysimp1; ysimp1; ysimp1; ysimp1; ysimp1; ysimp1;
      ysimp1; ysimp1  }
    { ysimp }

example (Q1 Q2 : β -> hhProp α) :
  H1 ∗ (H1 -∗ (Q1 -∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  ysimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  ysimp

example (Q1 Q2 : β -> hhProp α) :
   H1 ∗ (H1 -∗ (Q1 -∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  ysimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  ysimp

example :
  H1 ∗ H2 ==> H1 ∗ (Q1 -∗ (Q1 ∗ H2)) := by
  ysimp

example :
  H1 -∗ H4 ==> H5 ->
  (H2 ∗ ((H1 ∗ H2 ∗ H3) -∗ H4)) ∗ H3 ==> H5 := by
  move=> ?
  sby ysimp

example :
  (H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5))) ∗ (H2 -∗ H3) ∗ H4 ==> H5 :=
  by ysimp

example :
  (emp -∗ H1) ∗ H2 ==> H3 :=
  by ysimp; admit

example :
  ((H0 ∗ emp) -∗ emp -∗ H1) ∗ H2 ==> H3 := by
  ysimp; admit

example (v2 : Int) (s : Set α) (p1 p2 : α -> loc) (v1 : α -> val) :
  H0 ∗ H1 ∗ p1 i ~⟨i in s⟩~> v1 i ∗ p2 i ~⟨i in s⟩~> val.val_int (v2 * 1) ==> H2 ∗ (p2 i ~⟨i in s⟩~> v2) ∗ H3 := by
  ysimp
  any_goals admit

example (p : loc) (v : val) :
  v = v' →
  (H1 ∗ p ~⟨_ in s⟩~> v) ==> H1 ∗ p ~⟨_ in s⟩~> v' := by
  move=> ?
  ysimp

example (p1 p2 : loc) (v1 v2 v1' v2' : val):
  H1 ∗ p1 ~⟨_ in s⟩~> v1 ∗ H2 ∗ p2 ~⟨_ in s⟩~> v2 ∗ H3 ==> H1 ∗ H2 ∗ p1 ~⟨_ in s⟩~> v1' ∗ p2 ~⟨_ in s⟩~> v2' := by
  ysimp
  all_goals admit

example (v : val) :
  H1 ∗ 2 ~⟨_ in s⟩~> v ==> (1 + 1) ~⟨_ in s⟩~> v ∗ H1 := by
  ysimp

example (x : α -> loc) :
  x i ~⟨i in s⟩~> 1 ==> y ~⟨_ in s⟩~> 2 ∗ x i ~⟨i in s⟩~> 1 := by
  ysimp; sorry



set_option trace.ysimp true

example :
  H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5)) ∗ H4 ==> ((H2 -∗ H3) -∗ H5) := by
  ysimp

elab "put_hints" ls:hints : tactic => do
  match ls with
  | `(hints| [ $[$hs],* ]) =>
    hintExt.set hs.toList
  | _ => throwError "ysimp: unreachable"

example (Q : Int -> Bool -> _) :
  Q 4 true ==> Q 3 false ->
  H1 ∗ Q 4 true ==> ∃ʰ x b, Q x b ∗ H1 := by
  move=> ?
  ysimp

-- example :
--   emp ==> (∃ʰ x, x ~~> 1) ∗ (∃ʰ x, x ~~> 2) := by
--   ysimp_start
--   ysimp_step
--   ysimp_step
--   ysimp_step
--   ysimp_step
end
end
