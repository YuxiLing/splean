import Lean.Elab.Tactic
import Qq

import SSReflect.Lang

import LeanLgtm.Basic
import LeanLgtm.Util


open hprop_scope
open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

/- **============ `hsimp` trivrial goal simplification tactic ============** -/

lemma himpl_of_eq H1 H2 : H1 = H2 -> H1 ==> H2 :=
  by sby move=>-> ?

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


/- **============ `xsimp` implementation ============** -/

def XSimp (hl hr : hprop × hprop × hprop) :=
  let (hla, hlw, hlt) := hl
  let (hra, hrg, hrt) := hr
  hla ∗ hlw ∗ hlt ==> hra ∗ hrg ∗ hrt

@[heapSimp]
def protect (x : α) := x

structure XSimpR where
  hla : Term
  hlw : Term
  hlt : Term
  hra : Term
  hrg : Term
  hrt : Term


def XSimpRIni : TacticM XSimpR := withMainContext do
  let goal <- getGoalStxAll
  let `(XSimp  ($hla, $hlw, $hlt) ($hra, $hrg, $hrt)) := goal | throwError "not a XSimp goal"
  return { hla := hla, hlw := hlw, hlt := hlt, hra := hra, hrg := hrg, hrt := hrt }


/- ============ Theory for `xsimp` ============ -/
lemma xsimp_start_lemma :
  XSimp (emp, emp, h1 ∗ emp) (emp, emp, h2 ∗ emp) ->
  h1 ==> h2 := by sorry

/- ------------ Lemmas for LHS step ------------ -/
lemma xsimp_l_hempty :
  XSimp (hla, hlw, hlt) hr ->
  XSimp (hla, hlw, emp ∗ hlt) hr := by sorry

lemma xsimp_l_hpure :
  (p -> XSimp (hla, hlw, hlt) hr) ->
  XSimp (hla, hlw, hpure p ∗ hlt) hr := by sorry

lemma xsimp_l_acc_wand :
  XSimp (hla, h ∗ hlw, hlt) hr ->
  XSimp (hla, hlw, h ∗ hlt) hr := by sorry

lemma xsimp_l_acc_other :
  XSimp (h ∗ hla, hlw, hlt) hr ->
  XSimp (hla, hlw, h ∗ hlt) hr := by sorry

lemma xsimp_l_hexists :
  (∀ x, XSimp (hla, hlw, j x ∗ hlt) hr) ->
  XSimp (hla, hlw, (hexists j) ∗ hlt) hr := by sorry

lemma xsimp_l_cancel_hwand_hempty :
  XSimp (hla, hlw, h ∗ hlt) hr ->
  XSimp (hla, (emp -∗ h) ∗ hlw, hlt) hr := by sorry

lemma xsimpl_l_cancel_hwand_hstar_hempty :
  XSimp (Hla, Hlw, ((H2 -∗ H3) ∗ Hlt)) HR ->
  XSimp (Hla, (((emp ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR := by
  sorry

lemma xsimp_l_keep_wand :
  XSimp (H ∗ Hla, Hlw, Hlt) HR →
  XSimp (Hla, H ∗ Hlw, Hlt) HR :=
    by sorry

lemma xsimp_l_hwand_reorder :
  h1 = h1' ->
  XSimp (hla, ((h1' -∗ h2) ∗ hlw), hlt) hr ->
  XSimp (hla, (h1 -∗ h2) ∗ hlw, hlt) hr := by sorry

lemma xsimp_l_cancel_hwand_hstar :
    XSimp (Hla, Hlw, (H2 -∗ H3) ∗ Hlt) HR →
    XSimp ((H1 ∗ Hla), (((H1 ∗ H2) -∗ H3) ∗ Hlw), Hlt) HR :=
  by sorry

lemma xsimp_l_cancel_hwand :
    XSimp (emp, Hlw, Hla ∗ H2 ∗ Hlt) HR →
    XSimp ((H1 ∗ Hla), ((H1 -∗ H2) ∗ Hlw), Hlt) HR :=
  by sorry

lemma xsimp_l_cancel_qwand :
  XSimp (emp, Hlw, (Hla ∗ Q2 x ∗ Hlt)) HR ->
  XSimp ((Q1 x ∗ Hla), ((Q1 -∗∗ Q2) ∗ Hlw), Hlt) HR := by sorry

lemma xpull_protect (h : H1 ==> protect H2) : H1 ==> H2 :=
  by simp [protect] at h; assumption

/- ------------ Lemmas for RHS step ------------ -/

lemma xsimp_r_hempty :
  XSimp hl (hra, hrg, hrt) ->
  XSimp hl (hra, hrg, emp ∗ hrt) := by sorry

lemma xsimp_r_hwand_same :
  XSimp hl (hra, hrg, hrt) ->
  XSimp hl (hra, hrg, (h -∗ h) ∗ hrt) := by sorry

lemma xsimp_r_hpure :
  p -> XSimp hl (hra, hrg, hrt) ->
  XSimp hl (hra, hrg, hpure p ∗ hrt) := by sorry

lemma xsimp_r_hexists α (x : α) hl hra hrg hrt j :
  XSimp hl (hra, hrg, j x ∗ hrt) ->
  XSimp hl (hra, hrg, (hexists j) ∗ hrt) := by sorry

lemma xsimp_r_keep :
  XSimp hl (h ∗ hra, hrg, hrt) ->
  XSimp hl (hra, hrg, h ∗ hrt) := by sorry

lemma xsimpl_r_hgc_or_htop :
    XSimp HL (Hra, (H ∗ Hrg), Hrt) ->
    XSimp HL (Hra, Hrg, (H ∗ Hrt)) :=
  by sorry

lemma xsimpl_r_htop_drop :
  XSimp HL (Hra, Hrg, Hrt) ->
  XSimp HL (Hra, Hrg, (⊤ ∗ Hrt)) :=
  by sorry

/- ------------ Lemmas for LHS/RHS step ------------ -/

lemma xsimp_lr_hwand_hfalse :
  XSimp (Hla, emp, emp) ((⌜False⌝ -∗ H1) ∗ emp, emp, emp) := by sorry

lemma xsimp_lr_cancel_same :
  XSimp (hla, hlw, hlt) (hra, hrg, hrt) ->
  XSimp (h ∗ hla, hlw, hlt) (hra, hrg, h ∗ hrt) := by sorry

lemma himpl_lr_refl :
  XSimp (hla, emp, emp) (hla, emp, emp) := by sorry

lemma xsimp_lr_hwand :
  XSimp (emp, emp, (H1 ∗ Hla)) (emp, emp, H2 ∗ emp) ->
  XSimp (Hla, emp, emp) ((H1 -∗ H2) ∗ emp, emp, emp) := by sorry

lemma xsimpl_lr_qwand_unit :
  XSimp (emp, emp, (Q1 () ∗ Hla)) (emp, emp, (Q2 () ∗ emp)) ->
  XSimp (Hla, emp, emp) ((Q1 -∗∗ Q2) ∗ emp, emp, emp) :=
  by sorry

lemma xsimpl_lr_qwand :
    (forall x, XSimp (emp, emp, (Q1 x ∗ Hla)) (emp, emp, (Q2 x ∗ emp))) ->
    XSimp (Hla, emp, emp) (((Q1 -∗∗ Q2) ∗ emp), emp, emp) :=
  by sorry

lemma himpl_lr_qwand_unify :
  XSimp (Hla, emp, emp) ((Q -∗∗ (Q ∗∗ Hla)) ∗ emp, emp, emp) :=
  by sorry


lemma himpl_lr_htop :
  XSimp (emp, emp, emp) (emp, Hrg, emp) ->
  XSimp (Hla, emp, emp) (emp, (⊤ ∗ Hrg), emp) := by sorry

lemma xsimpl_lr_hforall :
  (forall x, XSimp (emp, emp, Hla) (emp, emp, J x ∗ emp)) ->
  XSimp (Hla, emp, emp) ((hforall J) ∗ emp, emp, emp) :=
  by sorry

lemma xsimpl_lr_cancel_htop :
  XSimp (Hla, Hlw, Hlt) (Hra, (⊤ ∗ Hrg), Hrt) ->
  XSimp ((H ∗ Hla), Hlw, Hlt) (Hra, (⊤ ∗ Hrg), Hrt) :=
  by sorry

lemma xsimp_lr_exit :
  Hla ==> Hra ∗ Hrg ->
  XSimp (Hla, emp, emp) (Hra, Hrg, emp) := by sorry

lemma qstar_simp :
  (Q1 ∗∗ H) x = Q1 x ∗ H := by rfl


/- ------------ Tactic for picking a particular heap proposition ------------ -/

/- TODO: Pregenerate such lemmas automatically -/
/- Note: Copilot can generate them pretty good -/
lemma hstar_pick_1 :
  h1 ∗ h = h1 ∗ h := by
  sdone

lemma hstar_pick_2  :
  h1 ∗ h2 ∗ h = h2 ∗ h1 ∗ h := by
  sby srw hstar_comm_assoc

lemma hstar_pick_3 :
  h1 ∗ h2 ∗ h3 ∗ h = h3 ∗ h1 ∗ h2 ∗ h := by
  sby srw (hstar_comm_assoc h2); apply hstar_pick_2

lemma hstar_pick_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h = h4 ∗ h1 ∗ h2 ∗ h3 ∗ h := by
  sby srw (hstar_comm_assoc h3); apply hstar_pick_3

lemma hstar_pick_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h := by
  sby srw (hstar_comm_assoc h4); apply hstar_pick_4

lemma hstar_pick_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h := by
  sby srw (hstar_comm_assoc h5); apply hstar_pick_5

lemma hstar_pick_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h := by
  sby srw (hstar_comm_assoc h6); apply hstar_pick_6

lemma hstar_pick_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h := by
  sby srw (hstar_comm_assoc h7); apply hstar_pick_7

lemma hstar_pick_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h := by
  sby srw (hstar_comm_assoc h8); apply hstar_pick_8

lemma hstar_pick_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 ∗ h = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h := by
  sby srw (hstar_comm_assoc h9); apply hstar_pick_9

lemma hstar_pick_last_1 :
  h1 = h1 := by sdone

lemma hstar_pick_last_2 :
  h1 ∗ h2 = h2 ∗ h1 := by
  sby srw hstar_comm

lemma hstar_pick_last_3 :
  h1 ∗ h2 ∗ h3 = h3 ∗ h1 ∗ h2 := by
  sby srw (hstar_comm h2); apply hstar_pick_2

lemma hstar_pick_last_4 :
  h1 ∗ h2 ∗ h3 ∗ h4 = h4 ∗ h1 ∗ h2 ∗ h3 := by
  sby srw (hstar_comm h3); apply hstar_pick_3

lemma hstar_pick_last_5 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 = h5 ∗ h1 ∗ h2 ∗ h3 ∗ h4 := by
  sby srw (hstar_comm h4); apply hstar_pick_4

lemma hstar_pick_last_6 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 = h6 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 := by
  sby srw (hstar_comm h5); apply hstar_pick_5

lemma hstar_pick_last_7 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 = h7 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 := by
  sby srw (hstar_comm h6); apply hstar_pick_6

lemma hstar_pick_last_8 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 = h8 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 := by
  sby srw (hstar_comm h7); apply hstar_pick_7

lemma hstar_pick_last_9 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 = h9 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 := by
  sby srw (hstar_comm h8); apply hstar_pick_8

lemma hstar_pick_last_10 :
  h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 ∗ h10 = h10 ∗ h1 ∗ h2 ∗ h3 ∗ h4 ∗ h5 ∗ h6 ∗ h7 ∗ h8 ∗ h9 := by
  sby srw (hstar_comm h9); apply hstar_pick_9

def hstar_pick_lemma (i : Nat) (pickLast : Bool) : Ident :=
  if pickLast then
    mkIdent s!"hstar_pick_last_{i}".toName
  else
    mkIdent s!"hstar_pick_{i}".toName

lemma xsimp_pick_lemma :
  hla2 = hla1 ->
  XSimp (hla1, hlw, hlt) hr ->
  XSimp (hla2, hlw, hlt) hr := by sby move=>->


set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def xsimp_pick (i : Nat) (last? : Bool) : TacticM Unit :=
   {| apply xsimp_pick_lemma
      · apply $(hstar_pick_lemma i last?) |}

partial def hstar_search (hs : Term) (test : Nat -> Term -> optParam Bool false -> TacticM Unit) :=
  let rec loop (i : Nat) (hs : Term)  : TacticM Unit := do
    match hs with
    | `($h1 ∗ $h2) => do
      try
        test i h1
      catch _ => loop (i+1) h2
    | _ => test i hs true
  loop 1 hs

def xsimp_pick_same (h hla : Term) : TacticM Unit := do
  let h  <- Tactic.elabTerm h none
  hstar_search hla fun i h' last? => do
    let h' <- Tactic.elabTerm h' none
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h' h | throwError "not equal"
    xsimp_pick i last?

def xsimp_pick_applied (h hla : Term) : TacticM Unit := do
  let h <- Term.elabTerm h  none
  hstar_search hla fun i h' last? => do
    let h' <- Term.elabTerm h' none
    let numArgs + 1 := h'.getAppNumArgs' | throwError "not equal"
    let h' := h'.consumeMData.getAppPrefix numArgs
    let .true <-
      withAssignableSyntheticOpaque <| isDefEq h h' | throwError "not equal"
    xsimp_pick i last?

/- ============ LHS xsmip step ============ -/

def xsimp_hwand_hstars_l (hla hs : Term) :=
  hstar_search hs fun i h last? => do
    -- let hstar_pick := hstar_pick_lemma i last?
    {| apply xsimp_l_hwand_reorder
       · apply $(hstar_pick_lemma i last?) |}
    match h with
    | `(emp) => {| apply xsimpl_l_cancel_hwand_hstar_hempty |}
    | _ => xsimp_pick_same h hla; {| apply xsimp_l_cancel_hwand_hstar |}

def xsimp_apply_intro_names (lem : Name) (xs : Syntax) : TacticM Unit :=
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
        | _ => throwError "xsimp_l_exists: @ unreachable 2"
    | _ => throwError "xsimp_l_exists: @ unreachable 3"
  | `(Lean.explicitBinders| $[$xs]*) =>
      for x in xs do
        match x with
        | `(Lean.bracketedExplicitBinders| ($x:ident : $_) ) =>
          {| apply $lem; intro $x:ident |}
        | _ => throwError "xsimp_l_exists: @ unreachable 1"
  | _ => throwError "xsimp_l_exists: @ unreachable 3"

partial def xsimp_step_l (xsimp : XSimpR) (cancelWand := true) : TacticM Unit := do
  trace[xsimp] "LHS step"
  match xsimp.hlt, xsimp.hlw with
  | `($h ∗ $_), _ =>
    match h with
    | `(emp)         => {| apply xsimp_l_hempty |}
    | `(⌜$_⌝)        => {| apply xsimp_l_hpure; intro |}
    | `($h1 ∗ $h2)   =>
      {| rw [@hstar_assoc $h1 $h2] |}
      /- we know that here should be another LHS step -/
      xsimp_step_l (<- XSimpRIni) cancelWand
    | `(h∃ $xs , $_) => xsimp_apply_intro_names `xsimp_l_hexists xs
    | `($_ -∗ $_)    => {| apply xsimp_l_acc_wand |}
    | `($_ -∗∗ $_)   => {| apply xsimp_l_acc_wand |}
    | _              => {| apply xsimp_l_acc_other |}
  | `(emp), `($h1 ∗ $_) =>
    match h1 with
    | `($h1 -∗ $_) =>
      match h1 with
      | `(emp) => {| apply xsimp_l_cancel_hwand_hempty |}
      | `($_ ∗ $_) => xsimp_hwand_hstars_l xsimp.hla h1
      | _ => try
          let .true := cancelWand | failure
          xsimp_pick_same h1 xsimp.hla
          {| apply xsimp_l_cancel_hwand |}
        catch _ => {| apply xsimp_l_keep_wand |}
    | `($q1 -∗∗ $_) =>
      if cancelWand then
        xsimp_pick_applied q1 xsimp.hla
        {| apply xsimp_l_cancel_qwand |}
      else {| apply xsimp_l_keep_wand |}
    | _ => throwError "xsimp_step_l: @ unreachable"
  | _, _ => throwError "xsimp_step_l: @ unreachable"

/- ============ RHS xsmip step ============ -/
declare_syntax_cat hint

syntax term : hint
syntax "?" : hint

declare_syntax_cat hints
syntax "[" (ppSpace colGt hint),* "]" : hints

def xsimp_r_hexists_apply_hints : TacticM Unit := do
  let hints <- hintExt.get
  match hints with
  | [] => {| eapply xsimp_r_hexists |}
  | h :: hs =>
    hintExt.set hs
    match h with
    | `(hint| ?)       => {| eapply xsimp_r_hexists |}
    | `(hint| $t:term) => {| apply (@xsimp_r_hexists _ $t) |}
    | _ => throwError "xsimp_r_hexists_apply_hints: @ unreachable"

partial def xsimp_step_r (xsimp : XSimpR) : TacticM Unit := do
  trace[xsimp] "RHS step"
  match xsimp.hlw, xsimp.hlt, xsimp.hrt with
  | `(emp), `(emp), `($h ∗ $_) =>
    /- TODO: implement hook -/
    try
      match h with
      | `(emp) => {| apply xsimp_r_hempty |}
      | `(⌜P⌝) => {| apply xsimp_r_hpure |}
      | `($h1 ∗ $h2) =>
        {| rw [@hstar_assoc $h1 $h2] |}
         /- we know that here should be another RHS step -/
        xsimp_step_r (<- XSimpRIni)
      | `($h1 -∗ $_) =>
        match h1 with
        | `(⌜$_⌝) => {| apply xsimp_r_keep |}
        | _ => {| apply xsimp_r_hwand_same |}
      | `(⊤) =>
        match xsimp.hrg with
        | `(emp) =>
          {| apply xsimpl_r_hgc_or_htop |}
          repeat'' do
            xsimp_pick_same h xsimp.hla
            {| apply xsimp_lr_cancel_same |}
        | `(⊤ ∗ emp) => {| apply xsimpl_r_htop_drop |}
        | _ => throwError "xsimp_step_r: @ unreachable"
      | `(h∃ $_, $_) => xsimp_r_hexists_apply_hints
      | `(protect $_) => {| apply xsimp_r_keep |}
      | _ =>
        if h.isMVarStx then
          {| apply xsimp_r_keep |}
        else
        xsimp_pick_same h xsimp.hla
        {| apply xsimp_lr_cancel_same |}
    catch _ => {| apply xsimp_r_keep |}
  | _, _, _ => throwError "not implemented"

/- ============ LHS/RHS xsmip step ============ -/

def xsimp_step_lr (xsimp : XSimpR) : TacticM Unit := do
  trace[xsimp] "LHS/RHS step"
  match xsimp.hrg with
  | `(emp) =>
    match xsimp.hra with
    | `($h1 ∗ emp) =>
      if h1.isMVarStx then
        {| hsimp; apply himpl_lr_refl |}
        return ()
      match h1 with
      | `($h1 -∗ $_) =>
        match h1 with
        | `(⌜False⌝) => {| apply xsimp_lr_hwand_hfalse |}
        | _ => /- TODO: flip -/ {| apply xsimp_lr_hwand |}
      | `($h1 -∗∗ $_) =>
        try
          let .true := h1.isMVarStx | failure
          {| apply himpl_lr_qwand_unify |}
        catch _ =>
          {| first | apply xsimpl_lr_qwand_unit
                   | apply xsimpl_lr_qwand; unhygienic intro
             try simp only [qstar_simp] |}
      | `(h∀ $xs, $_) => /- TODO: flip -/ xsimp_apply_intro_names `xsimpl_lr_hforall xs
      | _ => /- TODO: flip -/ {| apply xsimp_lr_exit |}
    | `(emp) => {| first | apply himpl_lr_refl | apply xsimp_lr_exit |}
    | _ => /- TODO: flip -/ {| apply xsimp_lr_exit |}
  | `(⊤ ∗ emp) => {| first | apply himpl_lr_htop | apply xsimp_lr_exit |}
  | _ => /- TODO: flip -/ {| apply xsimp_lr_exit |}


/- ============ Tactic Notations ============ -/

elab "xsimp_step" : tactic => do
  let xsimp <- XSimpRIni
  /- TODO: optimise.
    Sometimes we tell that some transitions are not availible at the moment.
    So it might be possible to come up with something better than trying all
    transitions one by one -/
  withMainContext do
    xsimp_step_l  xsimp <|>
    xsimp_step_r  xsimp <|>
    xsimp_step_lr xsimp

elab "xsimp_handle_qimpl" : tactic => do
  match_expr <- getMainTarget with
  | qimpl tp _ q2 =>
    if q2.isMVar then
      {| apply qimpl_refl |}
    else if tp.isConstOf `Unit then
      {| scase |}
    else let r <- fresh `r; {| intros $r |}
  | himpl _ h2 =>
     if h2.isMVar then
      {| apply himpl_refl |}
     else return ()
  | Eq tp _ _ =>
    let_expr hprop := tp | throwError "not a goal for xsimp/xpull"
    {| apply himpl_antisym |}
  | Eq tp _ _ =>
    let .some (_, tp) := tp.arrow? | throwError "not a goal for xsimp/xpull"
    let_expr hprop := tp | throwError "not a goal for xsimp/xpull"
    {| ext; apply himpl_antisym |}
  | _ => throwError "not a goal for xsimp/xpull"

macro "xpull_start" : tactic =>
  `(tactic|
     (xsimp_handle_qimpl
      apply xpull_protect
      apply xsimp_start_lemma))

macro "xsimp_start" : tactic =>
  `(tactic|
    (xsimp_handle_qimpl
     try apply xsimp_start_lemma))

macro "xpull" : tactic =>
  `(tactic| (
    xpull_start
    repeat' xsimp_step
    hsimp
  ))

macro "xsimp" : tactic =>
  `(tactic| (
    xsimp_start
    repeat' xsimp_step
    try hsimp
  ))

elab "xsimp" ls:hints : tactic => do
  match ls with
  | `(hints| [ $[$hs],* ]) =>
    hintExt.set hs.toList
    {| xsimp_start
       repeat' xsimp_step
       try hsimp |}
  | _ => throwError "xsimp: unreachable"

/- **============ Test Cases ============** -/
section

lemma dup_lemma (p : Prop) : p -> p -> p := by sdone

partial def dup (n : Nat) : TacticM Unit := do
  match n with
  | 0 => {|skip|}
  | _ => dup (n-1); {| apply dup_lemma|}

elab "dup" n:num : tactic =>
  dup $ n.getNat -1

/- [hstar_pick] -/
section

local elab "pick" i:num : tactic =>
  let l := hstar_pick_lemma i.getNat false
  {|apply $l|}

local elab "pickl" i:num : tactic =>
  let l := hstar_pick_lemma i.getNat true
  {|apply $l|}

example :
  (forall H, H1 ∗ H2 ∗ H3 ∗ H4 = H -> H = Hresult -> True) -> True := by
  intro M
  dup 2 <;> eapply M
  { pick 3 }
  { admit }
  { pickl 4 }
  { admit }

/- `xsimp_pick` -/

local elab "xsimp_pick" i:num : tactic =>
  xsimp_pick i.getNat false

local elab "xsimp_pickl" i:num : tactic =>
  xsimp_pick i.getNat true

local elab "xsimp_pick_same" h:term : tactic => do
  let xsimp <- XSimpRIni
  xsimp_pick_same h xsimp.hla

local elab "xsimp_pick_applied" h:term : tactic => do
  let xsimp <- XSimpRIni
  xsimp_pick_applied h xsimp.hla

example (Q : Bool -> _):
  (forall HX HY,
    XSimp ((H1 ∗ H2 ∗ H3 ∗ Q true ∗ (⌜P⌝ -∗ HX) ∗ HY ∗ emp), Hlw, Hlt)
           (Hra, Hrg, Hrt)
  -> True) -> True := by
  move=> M
  eapply M
  xsimp_pick 2
  xsimp_pick_same H3
  xsimp_pick_applied Q
  xsimp_pick_same H2
  xsimp_pick_same H3
  xsimp_pick_same ⌜True⌝
  xsimp_pick_same (⌜P⌝ -∗ H1)
  admit

/- `xsimp/xpull` -/

local macro "xpull0" : tactic => `(tactic| xpull_start)
local macro "xsimp0" : tactic => `(tactic| xsimp_start)
local macro "xsimp1" : tactic => `(tactic| xsimp_step)
local elab "xsimpl" : tactic => do
  xsimp_step_l (<- XSimpRIni) true
local elab "xsimpr" : tactic => do
  xsimp_step_r (<- XSimpRIni)

example :
  (H1 ∗ emp ∗ (H2 ∗ (h∃ (y:Int) (z : Int) (n:Int), ⌜y = y + z + n⌝)) ∗ H3) ==> H :=
  by
    dup 2
    { xpull0; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      admit }
    { xpull; admit }

example :
  H1 ∗ H2 ∗ H3 ∗ H4 ==> H4 ∗ H3 ∗ H5 ∗ H2 :=
  by
    dup 3
    { xpull; admit }
    { xsimp0; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1
      xsimp1; xsimp1; admit }
    xsimp; admit

example :
  H1 ∗ H2 ∗ H3 ∗ H4 ==> H5 ∗ H3 ∗ H6 ∗ H7 := by
  xsimp /- TODO: flip to preserve order -/
  admit

example :
  H1 ∗ H2 ∗ H3 ∗ H4 ∗ H5 ==> H3 ∗ H1 ∗ H2 ∗ ⊤ := by
  xsimp

example (Q : Int -> _) :
  Q 4 ==> Q 3 ->
  H1 ∗ Q 4 ==> h∃ x, Q x ∗ H1 :=
  by intro; xsimp[3]=> // /- TODO: handle hints -/

example :
  (forall H, H1 ∗ H2 ==> H -> True) -> True :=
  by sapply; xsimp

example :
  (forall H, H1 ==> H1 ∗ H -> True) -> True :=
  by sapply; xsimp

example :
  H1 ∗ H2 ∗ ⊤ ==> H1 ∗ ⊤ :=
  by xsimp

example :
  H1 ∗ H2 ∗ ⊤ ==> H1 ∗ ⊤ ∗ ⊤ :=
  by xsimp

example :
  (H1 -∗ (H2 -∗ H3)) ∗ H1 ∗ H4 ==> (H2 -∗ (H3 ∗ H4)) :=
  by
    dup 2
    { xsimp0;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1; xsimp1; xsimp1; xsimp1; xsimp1;
      xsimp1; xsimp1  }
    { xsimp }

example :
  H1 ∗ (H1 -∗ (Q1 -∗∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  xsimp

example :
   H1 ∗ (H1 -∗ (Q1 -∗∗ Q2)) ∗ (Q1 x) ==> (Q2 x) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (H3 -∗ (H2 ∗ H3)) := by
  xsimp

example :
  H1 ∗ H2 ==> H1 ∗ (Q1 -∗∗ (Q1 ∗∗ H2)) := by
  xsimp

example :
  H1 -∗ H4 ==> H5 ->
  (H2 ∗ ((H1 ∗ H2 ∗ H3) -∗ H4)) ∗ H3 ==> H5 := by
  move=> ?
  sby xsimp

example :
  (H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5))) ∗ (H2 -∗ H3) ∗ H4 ==> H5 :=
  by xsimp

example :
  (emp -∗ H1) ∗ H2 ==> H3 :=
  by xsimp; admit

example :
  ((H0 ∗ emp) -∗ emp -∗ H1) ∗ H2 ==> H3 := by
  xsimp; admit

set_option trace.xsimp true

example :
  H1 ∗ H2 ∗ ((H1 ∗ H3) -∗ (H4 -∗ H5)) ∗ H4 ==> ((H2 -∗ H3) -∗ H5) := by
  xsimp

local elab "put_hints" ls:hints : tactic => do
  match ls with
  | `(hints| [ $[$hs],* ]) =>
    hintExt.set hs.toList
  | _ => throwError "xsimp: unreachable"

example (Q : Int -> Bool -> _) :
  Q 4 true ==> Q 3 false ->
  H1 ∗ Q 4 true ==> h∃ x b, Q x b ∗ H1 := by
  move=> ?
  xsimp[3, ?]=> //

end
end
