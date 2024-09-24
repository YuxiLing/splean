import Lean
-- lemmas on heaps
import Mathlib.Data.Finmap
import Qq

import Lgtm.Unary.Util
import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.WPUtil
import Lgtm.Hyper.Subst
import Lgtm.Hyper.ArraysFun
import Lgtm.Hyper.HProp
import Lgtm.Hyper.Loops

open Classical trm val prim
open Lean Elab Term



-- abbrev LabType := ℕ
local macro "LabType" : term => `(ℕ)

structure Labeled (α : Type*) where
  lab : LabType
  val : α

def labSet (l : ℕ) (s : Set α) : Set (Labeled α) := { ⟨l, x⟩ | x ∈ s }

notation (priority := high) "⟪" l ", " s "⟫" => labSet l s

@[disjE]
lemma disjoint_label_set :
  Disjoint ⟪l,s⟫ ⟪l',s'⟫ ↔ l ≠ l' ∨ Disjoint s s' := by
  sorry

@[simp]
lemma labSet_inter (l : ℕ) (s s' : Set α) :
  ⟪l, s⟫ ∩ ⟪l, s'⟫ = ⟪l, s ∩ s'⟫ := by
  sorry

@[simp]
lemma labSet_diff (l : ℕ) (s s' : Set α) :
   ⟪l, s⟫ \ ⟪l, s'⟫ = ⟪l, s \ s'⟫ := by
  sorry

@[simp]
lemma labSet_mem :
  x ∈ ⟪l, s⟫ ↔ x.lab = l ∧ x.val ∈ s := by
  sorry

/- --- Notations for Triples and WPs --- -/

declare_syntax_cat sht

syntax "[" num "| " ident " in " term " => " lang "]" : sht
syntax "[sht| " sht "]" : term

syntax "NWP " (sht ppLine)* ppGroup( "{ " ident ", " ppGroup(term) " }") : term
syntax ppGroup("{ " term " }") ppDedent(ppLine (sht ppLine)* ppGroup( "{ " ident ", " ppGroup(term) " }")) : term

macro_rules
  | `(sht| [$n | $i in $s => $t]) => `(SHT.mk ⟪$n, $s⟫ (fun $i:ident => [lang|$t]))

macro "WP [" n:num "|" i:ident " in " s:term " => " t:lang "]" ppSpace Q:term : term =>
  `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) $Q)

macro "WP [" n:num "|" i:ident " in " s:term " => " t:lang "]"  "{ " v:ident ", " Q:term " }" : term =>
  `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) fun $v => $Q)


@[app_unexpander hwp] def unexpandHWP : Lean.PrettyPrinter.Unexpander
  | `($(_) ⟪$n:num,$s⟫ (fun $i:ident => [lang|$t])) => do
    `(WP [$n| $i in $s => $t] ⋯)
  | _ => throw ( )

-- #check LGTM.SHT.mk
macro_rules
  | `([sht| [$n | $i in $s => $t] ]) => `(LGTM.SHT.mk ⟪$n, $s⟫ (fun $i:ident => [lang|$t]))

@[app_unexpander LGTM.SHT.mk] def unexpandSHT : Lean.PrettyPrinter.Unexpander :=
  fun x => match x with
  | `($(_) ⟪$n:num,$s⟫ fun $i:ident => [lang|$t]) => do `([sht| [$n | $i in $s => $t] ])
  | `({ s:= ⟪$n:num,$s⟫, ht := (fun $i:ident ↦ [lang|$t]) }) => `([sht| [$n | $i in $s => $t] ])
  | _ => throw ( )

macro_rules
  | `(NWP $sht* { $v, $Q }) => `(
    LGTM.wp [ $[ [sht| $sht] ],* ] (fun $v => $Q)
  )

@[app_unexpander LGTM.wp] def unexpandNWP : Lean.PrettyPrinter.Unexpander
  | `($(_) [ $[ [sht| $sht:sht] ],* ] fun $v:ident => $Q) =>
    `(NWP $sht* { $v, $Q })
  | _ => throw ( )

@[app_unexpander hwp] def unexpandLGTMWP : Lean.PrettyPrinter.Unexpander
  | `($(_) ⟪$n:num,$s⟫ $f fun $_ => NWP $_* { $_, $_ }) =>
    match f with
    | `(fun $i:ident => [lang|$t]) => `(WP [$n| $i in $s => $t] ⋯)
    | _ => throw ( )
  | `($(_) ⟪$n:num,$s⟫ $f fun $v:ident => $Q) =>
    match f with
    | `(fun $i:ident => [lang|$t]) => `(WP [$n| $i in $s => $t] { $v:ident, $Q:term })
    | _ => throw ( )
  | _ => throw ( )


macro_rules
  | `({ $H } $sht* { $v, $Q }) => `(
    LGTM.triple [ $[ [sht| $sht] ],* ] $H (fun $v => $Q)
  )
@[app_unexpander LGTM.triple] def unexpandNTriple : Lean.PrettyPrinter.Unexpander
  | `($(_) [ $[ [sht| $sht:sht] ],* ] $H fun $v:ident => $Q) =>
    `({ $H } $sht* { $v, $Q })
  | _ => throw ( )

@[app_unexpander Labeled.mk] def unexpandLab : Lean.PrettyPrinter.Unexpander
  | `($(_) $l $v) => `(⟨$l, $v⟩)
  | _ => throw ( )

/- --- Lemmas for focus/unfocus --- -/

class FindLabel (l : LabType) (sht : LGTM.SHTs (Labeled α)) (i : outParam ℕ)
  (_ : outParam (i < sht.length)) where
  findLabel : ∃ s, sht[i].s = ⟪l, s⟫

instance (priority := high) FindLabelHead : FindLabel l (⟨⟪l,s⟫, ht⟩ :: shts) 0 (by simp) where
  findLabel := by move=> ⟨|⟩//

instance FindLabelTail (shts : LGTM.SHTs (Labeled α)) (pi : i < shts.length)
  [inst: FindLabel l shts i pi] :
  FindLabel l (⟨⟪l',s⟫, ht⟩ :: shts) (i+1) (by simp; omega) where
  findLabel := by scase: inst=> [s] /== ->; exists s=> //

lemma yfocus_lemma (l : LabType) (shts : LGTM.SHTs (Labeled α)) {pi} [FindLabel l shts i pi] :
  (List.Pairwise (Disjoint ·.s ·.s) shts) ->
  LGTM.wp shts Q = hwp shts[i].s shts[i].ht fun hv => LGTM.wp (shts.eraseIdx i) (Q $ hv ∪_shts[i].s ·) := by
  apply LGTM.wp_focus

lemma List.insertNth_getElem (l : List α) {_ : j <= l.length}
  {_ : i <= l.length}
  (_ : j < (l.insertNth i x).length :=
    (by srw List.length_insertNth //) ) :
  (l.insertNth i x)[j] = if h : j < i then l[j]'(by omega) else if h' : j = i then x else l[j-1]'(by omega) := by
  sorry

lemma List.eraseIdx_getElem (l : List α) {_ : j + 1 < l.length}
  {_ : i < l.length}
  (_ : j < (l.eraseIdx i).length :=
    (by srw List.length_eraseIdx //) ) :
  (l.eraseIdx i)[j] = if h : j < i then l[j]'(by omega) else l[j+1]'(by omega) := by
  sorry

lemma yunfocus_lemma (idx : ℕ) (l : LabType) (shts : LGTM.SHTs (Labeled α)) {pi : idx < shts.length}
  (Q' : hval (Labeled α) -> hval (Labeled α) -> hhProp (Labeled α)):
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (shts.Forall (Disjoint ⟪l,s⟫ ·.s)) ->
  (∀ hv hv', Q' hv hv' = Q (hv ∪_⟪l, s⟫ hv')) ->
  hwp ⟪l,s⟫ ht (fun hv => LGTM.wp shts fun hv' => Q' hv hv') =
  LGTM.wp (shts.insertNth idx ⟨⟪l, s⟫, ht⟩) Q := by
  move=> dj dj' Qeq; srw (LGTM.wp_focus idx)
  { srw List.getElem_insertNth_self //= List.eraseIdx_insertNth /=
    congr! 4=> //' }
  srw List.pairwise_iff_getElem at dj
  srw List.forall_iff_forall_mem at dj'
  srw List.pairwise_iff_getElem=> > ?
  srw ?(List.insertNth_getElem shts) //'
  { scase: [i < idx]=> ?
    { srw dif_neg //' [2]dif_neg; rotate_left; omega
      scase: [i = idx]=> [?|?]
      { srw dif_neg //' dif_neg; rotate_left; omega
        apply dj; omega }
      srw dif_pos //' /= dif_neg; rotate_left; omega
      apply dj'; apply List.getElem_mem }
    srw dif_pos //';  scase: [j < idx]=> [?|?]
    { srw dif_neg //'; scase: [j = idx]=> ?
      { srw dif_neg //'; apply dj; omega }
      srw dif_pos //' /= disjoint_comm; apply dj'; apply List.getElem_mem
      srw List.length_insertNth at _hi <;> omega }
    srw dif_pos //' }
  srw List.length_insertNth at _hj <;> omega


lemma LGTM.wp_hv_eq :
  LGTM.wp shts Q = LGTM.wp shts (fun hv => ∃ʰ hv', Q (hv ∪_shts.set hv')) := by
  sorry

lemma congr_hhimpl :
  H = H' ->
  H ==> H' := by move=>-> //

@[simp]
abbrev fun_lab_insert (l : LabType) (f g : Labeled α -> β) :=
  fun x => if x.lab = l then f x else g x
-- (_ \ _) ∪ (_ ∩ _)
set_option maxHeartbeats 1600000 in
lemma yfocus_set_lemma_aux (idx : ℕ) (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α))
  {pi : idx < shts.length} :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
    (hwp ⟪l, s \ s'⟫ shts[idx].ht fun hv =>
    LGTM.wp ((shts.eraseIdx (idx)).insertNth idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) fun hv' =>
      Q $ fun_lab_insert l (hv' ∪_⟪l,s'⟫ hv) hv') ==> LGTM.wp shts Q := by
    move=> seq /[dup]?/List.pairwise_iff_getElem dj' /[dup] dj₁ /Set.disjoint_left dj
    srw (LGTM.wp_focus idx) //' seq -(Set.diff_union_inter ⟪l,s⟫ ⟪l,s'⟫) /==
    srw hwp_union; apply hwp_conseq=> //'; rotate_left
    { simp [disjE, Set.disjoint_sdiff_inter] }
    move=> hv₁ /=; srw (LGTM.wp_focus idx)
    { srw  List.getElem_insertNth_self //=; rotate_left
      { srw List.length_eraseIdx //' }
      srw List.eraseIdx_insertNth /=
      apply hwp_conseq=> hv₂ /=; apply hwp_conseq'=> hv₃ /=
      ysimp [(fun_lab_insert l ((hv₂ ∪_⟪l, s ∩ s'⟫hv₃) ∪_⟪l, s'⟫hv₁) (hv₂ ∪_⟪l, s ∩ s'⟫hv₃))]
      apply congr_hhimpl; congr!; funext ⟨m,x⟩=> /==
      scase_if=> /== ?
      scase_if=> /==
      { scase_if=> //' }
      scase_if=> //'; scase_if=> //' /dj // }
    srw List.pairwise_iff_getElem=> > ?
    srw List.length_insertNth at _hi <;> try omega
    srw List.length_eraseIdx at _hi <;> try omega
    rotate_left
    { srw List.length_eraseIdx=> //' }
    srw List.length_insertNth at _hj <;> try omega
    srw List.length_eraseIdx at _hj <;> try omega
    rotate_left
    { srw List.length_eraseIdx=> //' }
    srw ?(List.insertNth_getElem _) //'
    { scase: [i < idx]=> ?
      { srw dif_neg //'; scase: [i = idx]=> ?
        { srw dif_neg //' (List.eraseIdx_getElem _) <;> try omega
          sdo 3 srw dif_neg <;> try omega
          srw (List.eraseIdx_getElem _) <;> try omega
          srw dif_neg <;> try omega
          apply dj'; omega }
        srw dif_pos //' /= dif_neg //' dif_neg //'
        srw (List.eraseIdx_getElem _) <;> try omega
        srw dif_neg <;> try omega
        srw disjoint_comm; apply Set.disjoint_of_subset _ _ dj₁=> x //'
        srw shts_set_eq_sum /== => ?; exists (j -1)=> ⟨|⟩
        { srw List.length_eraseIdx=> //' }
        srw getElem!_pos //'  (List.eraseIdx_getElem _) //'
        srw dif_neg //' }
      srw dif_pos //' (List.eraseIdx_getElem _) //' dif_pos //'
      scase: [j < idx]=> ?
      { srw dif_neg //'; scase: [j = idx]=> ?
        { srw dif_neg //' (List.eraseIdx_getElem _) //' dif_neg //'
          apply dj'=> //' }
        srw dif_pos //'=> /=; apply Set.disjoint_of_subset _ _ dj₁=> x //'
        srw shts_set_eq_sum /== => ?; exists (i)=> ⟨|⟩
        { srw List.length_eraseIdx=> //' }
        srw getElem!_pos //'  (List.eraseIdx_getElem _) //' }
      srw dif_pos //'(List.eraseIdx_getElem _) //' }
    all_goals srw List.length_eraseIdx=> //'

lemma yfocus_set_lemma (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) {pi : idx < shts.length}
  [FindLabel l shts idx pi] :
  shts[idx].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts idx)) ⟪l, Set.univ⟫) ->
    H ==> (hwp ⟪l, s \ s'⟫ shts[idx].ht fun hv =>
    LGTM.wp ((shts.eraseIdx idx).insertNth idx ⟨⟪l, s ∩ s'⟫,shts[idx].ht⟩) fun hv' =>
      Q $ fun_lab_insert l (hv' ∪_⟪l,s'⟫ hv) hv') -> H ==> LGTM.wp shts Q := by
  move=> *; apply hhimpl_trans_r; apply yfocus_set_lemma_aux=> //

lemma yclean_up_lemma (l : LabType) (s : Set α)
  (shts : LGTM.SHTs (Labeled α)) (Q : hval (Labeled α) -> hhProp (Labeled α)) :
  (shts.Forall (Disjoint ⟪l,Set.univ⟫ ·.s)) ->
  (forall hr, Q' hr = Q (v ∪_⟪l, s⟫ hr)) ->
  H ==> LGTM.wp shts (fun hr => Q (fun_lab_insert l v hr)) ->
  H ==> LGTM.wp shts Q' := by
  move=> dj Qeq h; ychange h; apply hwp_conseq'=> hv /=
  ysimp [fun_lab_insert l v hv]; srw Qeq;
  apply congr_hhimpl; congr!; funext ⟨m, x⟩=> /==
  scase_if=> //== ?; scase_if; scase_if=> //
  srw shts_set_eq_sum /== => ??
  srw getElem!_pos //;
  srw List.forall_iff_forall_mem Set.disjoint_left /== at dj
  move=> /dj f; exfalso; apply f=> //; apply List.getElem_mem

lemma ywp1 :
  LGTM.wp [⟨s, ht⟩] = hwp s ht := by
  move=> !Q; srw LGTM.wp /==; apply hwp_ht_eq=> ?? //


open Lean Elab Tactic Meta Qq

attribute [-simp] fun_insert
macro "yfocus" n:num : tactic => do
  `(tactic| (erw [yfocus_lemma $n:term]=> /=; ⟨skip, try simp [disjE]⟩))

macro "yfocus" n:num ", " s:term : tactic => do
  `(tactic| (apply yfocus_set_lemma $n:term $s=> /=;
             ⟨try simp [disjE], try simp [disjE], skip⟩
   ))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "yunfocus" n:num ? : tactic => do
  let n := n.getD (<- `(num|1))
  {| srw (yunfocus_lemma ($n-1)) /== |}
  let gs <- getUnsolvedGoals
  let [gRest, gDj, gQeq, _] := gs | failure
  /- try to resolve disjointness -/
  setGoals [gDj]; {| simp [disjE] |}
  -- /- unify postcondition -/
  let (_, gQeq) <- gQeq.intros
  let tp <- gQeq.getType
  let_expr Eq _ _ lhs := tp | failure
  let hv := lhs.getAppArgs[0]!
  let (_, gQen) <- gQeq.generalize #[{expr := hv }]
  gQen.refl
  setGoals [gRest]

macro "ycleanup" n:num : tactic => do
  `(tactic|
    (apply (yclean_up_lemma $n);
     ⟨simp [disjE],
      (move=> ?
       generalize (_ ∪_⟪$n, _⟫ _) = x; rfl) ,
      (dsimp; try srw ywp1) , skip, skip, skip⟩))

macro "yin " n:num ":" colGe ts:tacticSeq : tactic =>
  `(tactic| (
    yfocus $n;
    ($ts) <;> try (first | yunfocus $n |ycleanup $n)))

--   ))


/- ################################################################# -/
/-* * Practical Proofs -/

/-* This last section shows the techniques involved in setting up the lemmas
    and tactics required to carry out verification in practice, through
    concise proof scripts. -/

/- ================================================================= -/
/-* ** Lemmas for Tactics to Manipulate [wpgen] Formulae -/

lemma ystruct_lemma (F : @hformula α) H Q :
  H ==> F Q →
  H ==> hmkstruct F Q := by
  move=> h
  ychange h
  unfold hmkstruct
  ysimp

lemma yval_lemma v H (Q : hval α -> hhProp α) :
  H ==> Q v →
  H ==> hwpgen_val v Q := by
  move=> h
  ychange h

lemma ylet_lemma H (F1 : @hformula α) F2of Q :
  H ==> F1 (fun v => F2of v Q) →
  H ==> hwpgen_let F1 F2of Q :=
by
  move=> h
  ychange h

lemma yseq_lemma H (F1 F2 : @hformula α) Q :
  H ==> F1 (fun _ => F2 Q) →
  H ==> hwpgen_seq F1 F2 Q :=
by
  move=> h
  ychange h

lemma xif_lemma b H F1 F2 Q :
  (b = true -> H ==> F1 Q) →
  (b = false -> H ==> F2 Q) →
  H ==> hwpgen_if (fun (_ : htrm α) => b) F1 F2 Q :=
by
  scase: b
  move=> /== h
  sby all_goals ychange h ; unfold hwpgen_if ; ysimp

lemma yapp_lemma : forall t Q1 H1 H Q,
  htriple s t H1 Q1 ->
  H ==> H1 ∗ (Q1 -∗ protect Q) ->
  H ==> hwpgen_app s t Q :=
by
  move=> T M
  unfold hwpgen_app=> ?????
  ysimp
  apply htriple_ramified_frame=> //


lemma ywp_lemma_fun (v1 v2 : hval α) (x : α -> var) (t : htrm α) H Q :
  (∀ i, v1 i = val_fun (x i) (t i)) →
  H ==> hwp s (fun i => subst (x i) (v2 i) (t i)) Q →
  htriple s (fun x => trm_app (v1 x) (v2 x)) H Q :=
by sorry

lemma ywp_lemma_fix : forall (v1 v2 : hval α) (f x : α -> var) (t : htrm α) H Q,
  (∀ i, v1 i = val_fix (f i) (x i) (t i)) ->
  f != x ->
  H ==> hwp s (fun i => subst (x i) (v2 i) $ subst (f i) (v1 i) $ (t i)) Q ->
  htriple s (fun i => trm_app (v1 i) (v2 i)) H Q :=
by sorry

lemma ytriple_lemma t H (Q:hval α → hhProp α) :
  H ==> hmkstruct (hwpgen_app s t) Q →
  htriple s t H Q :=
by
  move=> M
  srw -hwp_equiv
  ychange M
  unfold hmkstruct hwpgen_app
  ypull=> >
  srw -hwp_equiv => N
  ychange N
  apply hwp_ramified


/- ================================================================= -/
/-* ** Tactics to Manipulate [wpgen] Formulae -/

/-* The tactic are presented in chapter [WPgen]. -/

/- [xstruct] removes the leading [mkstruct]. -/

section tactics

open Lean Elab Tactic

macro "ystruct" : tactic => do
  `(tactic| apply ystruct_lemma)


set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "ystruct_if_needed" : tactic => do
  match <- getGoalStxAll with
  | `($_ ==> hmkstruct $_ $_) => {| apply ystruct_lemma |}
  | _ => pure ( )
macro "ylet" : tactic => do
  `(tactic| (ystruct_if_needed; apply ylet_lemma; dsimp))

macro "yseq" : tactic => do
  `(tactic| (ystruct_if_needed; apply yseq_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "yseq_xlet_if_needed" : tactic => do
  match <- getGoalStxAll with
  | `($_ ==> hwpgen_let $_ $_ $_) => {| ylet |}
  | `($_ ==> hwpgen_seq $_ $_ $_) => {| yseq |}
  | _ => pure ( )

macro "yif" : tactic => do
  `(tactic|
  (yseq_xlet_if_needed; ystruct_if_needed; apply yif_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "yapp_try_clear_unit_result" : tactic => do
  let .some (_, _) := (← Lean.Elab.Tactic.getMainTarget).arrow? | pure ( )
  -- let_expr val := val | pure ()
  {| move=> _ |}

macro "ytriple" :tactic =>
  `(tactic| (intros; apply ytriple_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "ywp_equiv" :tactic => do
  let_expr hhimpl _ _ wp := (<- getMainTarget) | pure ( )
  let_expr hwp _ _ _ _ := wp | pure ( )
  {| rw [hwp_equiv] |}


set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "ytriple_if_needed" : tactic => do
  let_expr htriple _ _ _ _ _ := (<- getMainTarget) | pure ( )
  {| ytriple |}

lemma yapp_simpl_lemma (F : hformula) :
  H ==> F Q ->
  H ==> F Q ∗ (Q -∗ protect Q) := by sorry

elab "ysimp_step_no_cancel" : tactic => do
  let ysimp <- YSimpRIni
  /- TODO: optimise.
    Sometimes we tell that some transitions are not availible at the moment.
    So it might be possible to come up with something better than trying all
    transitions one by one -/
  withMainContext do
    ysimp_step_l  ysimp false <|>
    ysimp_step_r  ysimp <|>
    ysimp_step_lr ysimp

macro "ysimp_no_cancel_wand" : tactic =>
  `(tactic| (
    ysimp_start
    repeat' ysimp_step_no_cancel
    try rev_pure
    try hsimp
  ))

section yapp

macro "ywp" : tactic =>
  `(tactic|
    (intros
     first | apply ywp_lemma_fix; rfl
           | apply ywp_lemma_fun; rfl))

macro "yapp_simp" : tactic => do
  `(tactic|
      first | apply yapp_simpl_lemma; try hsimp
            | ysimp_no_cancel_wand; try unfold protect; yapp_try_clear_unit_result)

macro "yapp_pre" : tactic => do
  `(tactic|
    (yseq_xlet_if_needed
     ywp_equiv
     ytriple_if_needed
     ystruct_if_needed))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "yapp_try_subst" : tactic => do
  {| (unhygienic (skip=>>)
      move=>->) |}

macro "yapp_debug" :tactic => do
  `(tactic|
    (yapp_pre
     eapply yapp_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

elab "yapp_pick" e:term ? : tactic => do
  let thm <- (match e with
    | .none => pickHTripleLemma
    | .some thm => return thm.raw.getId : TacticM Name)
  {| eapply $(mkIdent thm) |}

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
-- elab "yapp_nosubst"  : tactic => do
--   {| (yapp_pre
--       eapply yapp_lemma; yapp_pick_debug
--       rotate_left; yapp_simp=>//) |}

macro "yapp_nosubst" e:term ? : tactic =>
  `(tactic|
    (yapp_pre
     eapply yapp_lemma; yapp_pick $(e)?
     rotate_right; yapp_simp; hide_mvars=>//))

macro "yapp" : tactic =>
  `(tactic|
    (yapp_nosubst;
     try yapp_try_subst
     first
       | done
       | all_goals try srw hwp_equiv
         all_goals try subst_vars))

elab "yapp" colGt e:term ? : tactic => do
  {|
    (yapp_nosubst $(e)?;
     try yapp_try_subst
     first
       | done
       | all_goals try srw hwp_equiv
         all_goals try subst_vars) |}

end yapp


end tactics

@[simp]
abbrev var_funs (xs:List var) (n:Nat) : Prop :=
     xs.Nodup
  /\ xs.length = n
  /\ xs != []

@[simp]
def trms_vals (vs : List var) : List trm :=
  vs.map trm_var

instance : Coe (List var) (List trm) where
  coe := trms_vals

-- lemma trms_vals_nil :
--   trms_vals .nil = .nil := by rfl
@[simp]
def trms_to_vals (ts:List trm) : Option (List val) := do
  match ts with
  | [] => return []
  | (trm_val v) :: ts' => v :: (<- trms_to_vals ts')
  | _ => failure

/- ======================= WP Generator ======================= -/
/- Below we define a function [wpgen t] recursively over [t] such that
   [wpgen t Q] entails [wp t Q].

   We actually define [wpgen E t], where [E] is a list of bindings, to
   compute a formula that entails [wp (isubst E t)], where [isubst E t]
   is the iterated substitution of bindings from [E] inside [t].
-/

open AList

-- abbrev ctx := AList (fun _ : var ↦ val)

/- Definition of Multi-Substitution -/


lemma trm_apps1 :
  trm_app t1 t2 = trm_apps t1 [t2] := by rfl

lemma trm_apps2 :
  trm_apps (trm_app t1 t2) ts = trm_apps t1 (t2::ts) := by rfl


lemma ywp_lemma_funs (xs : α -> List var) (vs : α -> List val) (t t1 : htrm α)
  (ts : α -> List trm):
  (∀ i, t i = trm_apps (v0 i) (ts i)) ->
  (v0 = fun i => val_funs (xs i) (t1 i)) ->
  (∀ i, trms_to_vals (ts i) = vs i) ->
  (∀ i, var_funs (xs i) (vs i).length) ->
  H ==> hwp s (fun i => Unary.isubst ((xs i).mkAlist (vs i)) $ t1 i) Q ->
  htriple s t H Q := by sorry

lemma xwp_lemma_fixs (xs : α -> List var) (vs : α -> List val) (t t1 : htrm α)
  (ts : α -> List trm) (f : α -> var) :
  (∀ i, t i = trm_apps (v0 i) (ts i)) ->
  (v0 = fun i => val_fixs (f i) (xs i) (t1 i)) ->
  (∀ i, trms_to_vals (ts i) = (vs i)) ->
  (∀ i, var_funs (xs i) (vs i).length) ->
  (∀ i, f i ∉ (xs i)) ->
  H ==> hwp s (fun i => Unary.isubst ((f i :: xs i).mkAlist (v0 i :: vs i)) $ t1 i) Q ->
  htriple s t H Q := by sorry

-- lemma wp_of_wpgen :
--   H ==> wpgen t Q →
--   H ==> wp t Q := by sorry


macro "ywp" : tactic =>
  `(tactic|
    (intros
     try simp_rw [trm_apps1]
     repeat simp_rw [trm_apps2]
     try (first | (apply ywp_lemma_fixs; rfl; rfl; sdone; sdone; sdone)=> //'
                | (apply ywp_lemma_funs; rfl; rfl; rfl; sdone)=> //')
     apply hwp_of_hwpgen
     all_goals try simp
       [hwpgen,
        subst,
        isubst, trm_apps, AList.lookup, List.dlookup]
     all_goals try simp [_root_.subst, trm_apps]))

macro "yval" : tactic => do
  `(tactic| (ystruct_if_needed; yseq_xlet_if_needed; (try ywp); apply yval_lemma))

/- ================================================================= -/
/- ====================== Resolving [hhlocal] =====================  -/

attribute [hhlocalE]
  hhlocal_bighstar
  hhlocal_hhstar
  hhlocal_hhexists

@[hhlocalE]
lemma hhlocal_hhsingle : hhlocal s' (hhsingle s x v) = (s ⊆ s') :=
  by apply hhlocal_bighstar

@[hhlocalE]
lemma hhlocal_hharrayFun : hhlocal s' (hharrayFun s f n x) = (s ⊆ s') :=
  by apply hhlocal_bighstar

@[hhlocalE]
lemma hhlocal_emp : hhlocal s emp = true :=
  by simp=> ?//

@[simp]
lemma cdot_set_mem (n : ℕ) (s : Set α) : (x ∈ (n • s)) = (x ∈ s ∧ n > 0) := sorry

/- ================================================================= -/
/- ====================== Tactics for Loops ======================== -/

/- Fisrt we provide instances for a typeclass which dirives
   [yfor_lemma] and [ywhile_lemma]   -/
set_option maxHeartbeats 1600000 in
lemma GenInstArr_eqSum (hv : hval α) (f : Int -> val)
  (op : hval α -> Int -> val) [PartialCommMonoid val]:
  (∀ i, PartialCommMonoid.valid (f i)) →
  (∀ i, PartialCommMonoid.valid (op hv i)) →
  hharrayFun s (fun i ↦ f i + op hv i) n x =
    hharrayFun s (fun x ↦ f x) n x +
    ∑ i ∈ [[(0 : ℤ) , n]], (x j + 1 + i.natAbs ~⟨j in s⟩~> op hv i) := by
  move=> ??; srw hharrayFun_hhadd_sum //'
  srw ?hharrayFun ?harrayFun; congr! 4=> ! [] /== //

lemma GenInstArr_eqGen (s : Set α) (x : α -> loc) (hv : Int -> hval α) (f : Int -> val) (n : ℕ)
  (op : hval α -> Int -> val) [PartialCommMonoid val] :
  (∀ i, PartialCommMonoid.valid (f i)) →
  (∀ i, PartialCommMonoid.valid (op (hv i) i)) →
  ∀ j ∈ [[(0 : ℤ) , n]],
    ∃ v H,
      PartialCommMonoid.valid v ∧
      hharrayFun s (fun x ↦ f x) n x + ∑ i ∈ [[0, j]],
       (x j + 1 + i.natAbs ~⟨j in s⟩~> op (hv i) i) =
        x i + 1 + j.natAbs ~⟨i in s⟩~> v ∗ H := by
  move=> ?? > /== ??; srw hharrayFun_hhadd_sum //'
  move: (harrayFun_chip_off (p := x) (n := n)
    (f := ((fun i ↦ if i < j then  f i + op (hv ↑i) ↑i else f i))) s j)=> h
  specialize h ?_ ?_=> //; scase: h=> H -> //
  move=> ⟨|⟨|⟨|//⟩⟩⟩ //


namespace AddPCM

instance GenInst (op : hval α -> Int -> Int) (x : loc) :
  IsGeneralisedSum
    z n
    AddPCM.add AddPCM.valid
    (x ~⟨_ in s⟩~> 0)
    (fun i hv => x ~⟨_ in s⟩~> op hv i)
    (Int)
    (fun _ j =>  x ~⟨_ in s⟩~> j)
    (fun i j hv => x ~⟨_ in s⟩~> val.val_int (op hv i + j))
    (fun hv => x ~⟨_ in s⟩~> val.val_int (∑ i in [[z,n]], op hv i)) where
    eqGen := by
      move=> > ?
      exists (∑ i in [[z, j]], op (hv i) i) , emp
      srw sum_hhsingle; ysimp=> //
    eqInd := by srw hhadd_hhsingle //
    eqSum := by srw sum_hhsingle //

@[simp]
lemma validE : PartialCommMonoid.valid = AddPCM.valid := by trivial

@[simp]
lemma addE : (· + ·) = AddPCM.add := by trivial

instance GenInstArr (op : hval α -> Int -> Int)
  (n : ℕ)
  (f : Int -> Int) (x : α -> loc) :
  IsGeneralisedSum
    0 n
    AddPCM.add AddPCM.valid
    (hharrayFun s (f ·) n x)
    (fun i hv => x j + 1 + i.natAbs ~⟨j in s⟩~> op hv i)
    (Int)
    (fun k j =>  x i + 1 + k.natAbs ~⟨i in s⟩~> j)
    (fun i j hv => x k + 1 + i.natAbs ~⟨k in s⟩~> val.val_int (op hv i + j))
    (fun hv => hharrayFun s (fun i => val.val_int $ f i + op hv i) n x) where
    eqGen := by
      move=> hv j jin; move: (GenInstArr_eqGen s x hv (f ·) n (op · ·))=> H
      specialize H ?_ ?_ j jin=> //; scase!: H=> [] //
    eqInd := by srw hhadd_hhsingle //'
    eqSum := by move=> hv; apply GenInstArr_eqSum hv (f ·) (op · ·)=> //

end AddPCM

namespace OrPCM

instance GenInst (op : hval α -> Int -> Bool) (x : loc) :
  IsGeneralisedSum
    z n
    OrPCM.add OrPCM.valid
    (x ~⟨_ in s⟩~> false)
    (fun i hv => x ~⟨_ in s⟩~> op hv i)
    (Bool)
    (fun _ j =>  x ~⟨_ in s⟩~> j)
    (fun i j hv => x ~⟨_ in s⟩~> val.val_bool (op hv i || j))
    (fun hv => x ~⟨_ in s⟩~> val.val_bool (∃ i ∈ [[z,n]], op hv i)) where
    eqGen := by
      move=> > ?
      exists (∃ i ∈ [[z, j]], op (hv i) i) , emp
      srw or_hhsingle; ysimp=> //
    eqInd := by move=> >; srw hhadd_hhsingle_gen //
    eqSum := by move=> >; srw or_hhsingle //

@[simp]
lemma validE : PartialCommMonoid.valid = OrPCM.valid := by trivial

@[simp]
lemma addE : (· + ·) = OrPCM.add := by trivial

instance GenInstArr (op : hval α -> Int -> Bool)
  (n : ℕ)
  (f : Int -> Bool) (x : α -> loc) :
  IsGeneralisedSum
    0 n
    OrPCM.add OrPCM.valid
    (hharrayFun s (f ·) n x)
    (fun i hv => x j + 1 + i.natAbs ~⟨j in s⟩~> op hv i)
    (Bool)
    (fun k j =>  x i + 1 + k.natAbs ~⟨i in s⟩~> j)
    (fun i j hv => x k + 1 + i.natAbs ~⟨k in s⟩~> val.val_bool (op hv i || j))
    (fun hv => hharrayFun s (fun i => val.val_bool $ f i || op hv i) n x) where
    eqGen := by
      move=> hv j jin; move: (GenInstArr_eqGen s x hv (f ·) n (op · ·))=> H
      specialize H ?_ ?_ j jin=> //; scase!: H=> [] //
    eqInd := by move=>>; srw hhadd_hhsingle_gen //'
    eqSum := by move=> hv; apply GenInstArr_eqSum hv (f ·) (op · ·)=> //

@[app_unexpander hharrayFun]
def hharrayFunUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $f $n fun $_ => $p) =>
    match f with
    | `(fun $x:ident => $f) =>
      `(arr($p ⟨$s:term⟩ , $x:ident in $n => $f))
    | _ => throw ( )
  | _ => throw ( )

end OrPCM

declare_syntax_cat loop_op
declare_syntax_cat loop_arg
declare_syntax_cat loop_args
declare_syntax_cat loop_type


syntax "+" : loop_op
syntax "||" : loop_op
syntax "+." : loop_op

syntax "(" ident ":=" term ")" : loop_arg
syntax loop_arg loop_args : loop_args

syntax "yfor" : loop_type
syntax "ywhile" : loop_type
syntax loop_type loop_op ? "with" (loop_arg colGe)* : tactic

macro_rules
  | `(tactic| yfor$loop_op ? with $[($x := $v)]*) => do
    let yforLemm <- `(yfor_lemma (z := _) (n := _) $[ ( $x:ident := $v:term ) ]*)
    let tac <- `(tactic| (eapply $yforLemm; ⟨
      try simp; try omega, -- s' ⊥ sᵢ
      try simp; try omega, -- Pairwise disj
      omega, -- z <= n
      simp [hhlocalE], -- hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      try solve | (simp=> > ?? ->->), -- Qeq
      simp [LGTM.SHTs.set], -- step
      skip, -- pre
      (move=> > /==)⟩ -- post
      ))
    match loop_op with
    | .none => pure tac
    | .some loop_op =>
      match loop_op with
      | `(loop_op| ||) => `(tactic| open OrPCM      in $tac:tactic)
      | `(loop_op| +)  => `(tactic| open AddPCM     in $tac:tactic)
      | `(loop_op| +.) => `(tactic| open AddRealPCM in $tac:tactic)
      | _ => Macro.throwErrorAt loop_op "unsupported loop operation"

/- ============ Tests for y-loops lemmas ============ -/
section


local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q
example (F : False) :
  LGTM.triple
    [⟨{11}, fun _ => trm_for vr (val.val_int 1) (val.val_int 10) c⟩ ,
     ⟨∑ i in [[1, 10]], {i}, ht⟩ ,
     ⟨∑ i in [[1, 10]], {-i}, ht⟩]
    ((x ⟨_ in {1}⟩|-> 0) ∗ R ∗↑ s)
    (fun hv => ((x ⟨_ in {1}⟩|->  ∑ j in [[0, 10]], (hv j))) ∗ R' ∗↑ s) := by
  yfor+ with
    (Inv := fun _ => emp)
    (valid := valid)
    (add := add)
    (Q := fun i hv => x ⟨_ in {11}⟩|-> (hv i + hv (-i)))
    (H₀ := x ⟨_ in {11}⟩|-> 0)
    (R := R)
    (R' := R')=> //

example (F : False) (n : ℕ) (f g : ℤ -> ℤ) :
  LGTM.triple
    [⟨{-2}, fun _ => trm_for vr (val.val_int 0) (val.val_int n) c⟩ ,
     ⟨∑ i in [[(0:ℤ) , n]], {i}, ht⟩ ,
     ⟨∑ i in [[(0:ℤ) , n]], {-1}, ht⟩]
    ((hharrayFun {-2} (f ·) n (fun _ => x)) ∗ R ∗↑ s)
    (fun hv => (hharrayFun {-2} (g ·) n (fun _ => x)) ∗ R' ∗↑ s) := by
  yfor+ with
    (valid := valid)
    (add := add)
    (Inv := fun _ => emp)
    (Q := (fun i hv => (x + 1 + i.natAbs) ⟨_ in {-2}⟩|-> hv i))
    (H₀ := hharrayFun {-2} (f ·) n (fun _ => x))
    (R := R)
    (R' := R')=> //

end


section

variable {H : hhProp (Labeled Int)}

instance : Coe (Labeled ℤ) ℤ where
  coe l := l.val

-- #check [sht| [1 | i in {(1 : ℤ),3} => let x := ⟨i⟩ in x + 1] ]
example :
  emp ==>
    NWP [1 | i in {(1 : ℤ) ,3} => let x := ⟨i⟩ in x + 1]
        [2 | i in {1,3} => let x := ⟨i⟩ in x + 1]
    { v, ⌜v ⟨1,1⟩ = 2 ∧ v ⟨2,1⟩ = 2 ∧ v ⟨1,3⟩ = 4⌝ } := by
  yin 1: ywp; yval
  yfocus 2, {3}=> /==
  ywp; yval
  yapp htriple_add
  yin 2: ywp; yval; yapp htriple_add
  yapp htriple_add
  srw fun_insert /==; ysimp

-- #check
--   { (H ∗ H) }
--     [1 | i in {1,3} => let x := ⟨i.val⟩ in x + 1]
--     [2 | i in {1,3} => let x := ⟨i.val⟩ in x + 1]
--   { v, ⌜v ⟨1,1⟩ = 2 ∧ v ⟨1,1⟩ = 2 ∧ v ⟨1,1⟩ = 2⌝ }

end
