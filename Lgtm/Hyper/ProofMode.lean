import Lean
-- lemmas on heaps
import Mathlib.Data.Finmap
import Qq

import Lgtm.Common.LabType
import Lgtm.Common.Util

import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.WPUtil
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Subst.YLemmas
import Lgtm.Hyper.ArraysFun
import Lgtm.Hyper.HProp
import Lgtm.Hyper.Loops.YLemmas
import Lgtm.Hyper.Merge

open Classical trm val prim
open Lean hiding Meta.subst
open Elab Term

local macro "LabType" : term => `(ℕ)


lemma hwp_labSet_single :
  hwp ⟪l, {a}⟫ ht Q = hwp ⟪l, {a}⟫ (fun _ => ht ⟨l,a⟩) Q := by
  srw hwp_ht_eq=> []//

lemma hwp_labSet_single_prod :
  hwp ⟪l, {a} ×ˢ s⟫ ht Q = hwp ⟪l, {a} ×ˢ s⟫ (fun i => ht ⟨l,a, i.val.2⟩) Q := by
  srw hwp_ht_eq=> []// ? [] //

lemma triple_labSet_single_prod :
  htriple ⟪l, {a} ×ˢ s⟫ ht H Q = htriple ⟪l, {a} ×ˢ s⟫ (fun i => ht ⟨l,a, i.val.2⟩) H Q := by
  srw -hwp_equiv hwp_ht_eq // => []// ? [] //

lemma triple_labSet_single :
  htriple ⟪l, {a}⟫ ht H Q = htriple ⟪l, {a}⟫ (fun _ => ht ⟨l,a⟩) H Q := by
  srw -hwp_equiv hwp_ht_eq // => []//


macro "simpWP" : tactic => `(tactic|
  simp only [hwp_labSet_single, hwp_labSet_single_prod, triple_labSet_single, triple_labSet_single_prod]
)

lemma hhsingle_singleton :
  hhsingle ⟪l, {a}⟫ p = hhsingle ⟪l, {a}⟫ (p ⟨l, a⟩) := by
  move=>!v /=; srw hhsingle bighstar_eq=> [] //

/- --- Notations for Triples and WPs --- -/

declare_syntax_cat sht

syntax "[" num "| " ident " in " term " => " lang "]" : sht
syntax "[sht| " sht "]" : term

syntax "NWP " (sht ppLine)* ppGroup( "{ " ident ", " ppGroup(term) " }") : term
syntax ppGroup("{ " term " }") ppDedent(ppLine (sht ppLine)* ppGroup( "{ " ident ", " ppGroup(term) " }")) : term
-- syntax "WP [" term "|" ident " in " term " => " lang "]" ppSpace term : term
syntax "WP [" term "|" ident " in " term " => " lang "]" "{ " ident ", " term " }" : term

macro_rules
  | `(sht| [$n | $i in $s => $t]) => `(SHT.mk ⟪$n, $s⟫ (fun $i:ident => [lang|$t]))

macro_rules
  | `(term|WP [$n| $i in $s => $t] { $v:ident, $Q:term }) =>
  `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) (fun $v:ident => $Q))


-- macro_rules
--   | `(WP [$n| $i in $s => $t] $Q) => `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) $Q)
-- macro "WP [" n:term "|" i:ident " in " s:term " => " t:lang "]" ppSpace Q:term : term =>
--   `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) $Q)

-- macro "WP [" n:term "|" i:ident " in " s:term " => " t:lang "]"  "{ " v:ident ", " Q:term " }" : term =>
--   `(hwp ⟪$n,$s⟫ (fun $i:ident => [lang|$t]) (fun $v:ident => $Q))


@[app_unexpander hwp] def unexpandHWP : Lean.PrettyPrinter.Unexpander
  | `($(_) ⟪$n:term,$s⟫ (fun $i:ident => [lang|$t])) => do
    `(WP [$n| $i in $s => $t] { $i,  ⋯ } )
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
  | `($(_) ⟪$n:num,$s⟫ $f fun $j:ident => NWP $_* { $_, $_ }) =>
    match f with
    | `(fun $i:ident => [lang|$t]) => `(WP [$n| $i in $s => $t] { $j, ⋯ })
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

@[app_unexpander htriple] def unexpandHTriple : Lean.PrettyPrinter.Unexpander
  | `($(_) ⟪$n:num, $s:term⟫ $t $H fun $v:ident => $Q) =>
      match t with
      | `(fun $i:ident => [lang|$t]) =>
        match Q with
        | `(NWP $_* { $_, $_ }) => `({ $H } [$n| $i in $s => $t] { $v, ⋯ })
        | _ => `({ $H } [$n| $i in $s => $t] { $v, $Q })
      | _ => throw ( )
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

lemma yunfocus_lemma (idx : ℕ) (l : LabType) (shts : LGTM.SHTs (Labeled α)) {pi : idx-1 < shts.length}
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
  `(tactic| ((try srw LGTM.triple); erw [yfocus_lemma $n:term]=> /=; ⟨skip, try simp [disjE]⟩))

macro "yfocus" n:num ", " s:term : tactic => do
  `(tactic| (apply yfocus_set_lemma $n:term $s=> /=;
             ⟨try simp [disjE], try simp [disjE], skip⟩
   ))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "yunfocus" n:num ? : tactic => do
  let n := n.getD (<- `(num|1))
  {| try srw -hwp_equiv |}
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

lemma yif_lemma (s : Set α) b H F1 F2 Q :
  (b = true -> H ==> F1 Q) →
  (b = false -> H ==> F2 Q) →
  H ==> hwpgen_if s (fun (_ : α) => b) F1 F2 Q :=
by
  scase: b
  move=> /== h
  sby all_goals ychange h ; unfold hwpgen_if ; ysimp

lemma yif_lemma_true (s : Set α) (b : htrm α) H F1 F2 Q :
  (∀ a ∈ s, b a = true) ->
  (H ==> F1 Q) ->
  H ==> hwpgen_if s b F1 F2 Q :=
by
  move=> bE h; ychange h
  srw hwpgen_if; ysimp [true]=> //

lemma yif_lemma_false (s : Set α) (b : htrm α) H F1 F2 Q :
  (∀ a ∈ s, b a = false) ->
  (H ==> F2 Q) ->
  H ==> hwpgen_if s b F1 F2 Q :=
by
  move=> bE h; ychange h
  srw hwpgen_if; ysimp [false]=> //


lemma yapp_lemma : forall t Q1 H1 H Q,
  htriple s t H1 Q1 ->
  H ==> H1 ∗ (Q1 -∗ protect Q) ->
  H ==> hwpgen_app s t Q :=
by
  move=> T M
  unfold hwpgen_app=> ?????
  ysimp
  apply htriple_ramified_frame=> //

lemma yref_lemma_aux s (x : α → var) (v : α → val) (t : α → trm) H Q :
  (∀ p : α → loc, H ==> ((p i ~⟨i in s⟩~> v i) -∗
    protect (hwp s (fun i ↦ subst (x i) (p i) (t i))
    (Q ∗ ∃ʰ (u : α → val), p i ~⟨i in s⟩~> u i)))) →
  H ==> hwpgen_ref s x (fun i ↦ trm_val (v i)) t Q :=
by
  move=> M h /M
  unfold hwpgen_ref=> /hhforall_inv {}M
  exists v=> /==
  sby srw hhstar_hhpure_l

lemma yref_lemma (x : α → var) (v : α → val) (t : α → trm) H Q :
  (∀ p : α → loc, H ∗ (p i ~⟨i in s⟩~> v i) ==>
    (hwp s (fun i ↦ subst (x i) (p i) (t i))
    (Q ∗ ∃ʰ (u : α → val), p i ~⟨i in s⟩~> u i))) →
  H ==> hwpgen_ref s x (fun i ↦ trm_val (v i)) t Q :=
by
  move=> himp; apply yref_lemma_aux=> p
  ysimp; ychange himp

lemma yref_lemma_singleton (x : αˡ → var) (v : αˡ → val) (t : αˡ → trm) H Q :
  (∀ p : loc, H ∗ (p ~⟨i in ⟪l, {a}⟫⟩~> v i) ==>
    (hwp ⟪l, {a}⟫ (fun _ ↦ subst (x ⟨l, a⟩) p (t ⟨l, a⟩))
    (Q ∗ ∃ʰ (u : αˡ → val), p ~⟨i in ⟪l, {a}⟫⟩~> u i))) →
  H ==> hwpgen_ref ⟪l, {a}⟫ x (fun i ↦ trm_val (v i)) t Q :=
by
  move=> imp; apply yref_lemma=> p;
  srw hhsingle bighstar_eq; apply hhimpl_trans
  { apply imp (p ⟨l,a⟩) }
  srw [2]hwp_labSet_single; apply hwp_conseq
  ypull=> u; ysimp[u]; scase: u=> ?? /==
  { move=>->-> // }
  srw hhsingle bighstar_eq //
  scase=> ?? /== ->->



lemma yref_lemma_nested (x : α → var) (v : α → val) (t : α → trm) H (Q : _ -> _ -> _) :
  shts.Forall (Disjoint ·.s s ) ->
  (∀ p : α → loc, H ∗ (p i ~⟨i in s⟩~> v i) ==>
    (hwp s (fun i ↦ subst (x i) (p i) (t i))
    (fun hv => (LGTM.wp shts fun hv' => Q hv hv' ∗ ∃ʰ (u : α → val), p i ~⟨i in s⟩~> u i)))) →
  H ==> hwpgen_ref s x (fun i ↦ trm_val (v i)) t (fun hv => LGTM.wp shts (Q hv)) :=
by
  move=> dj ?; apply yref_lemma=> ?
  apply hhimpl_trans=> //; apply hwp_conseq=> hv /=
  apply hwp_frame_in=> //
  srw shts_set_eqSum /==; move: dj
  srw List.forall_iff_forall_mem //

lemma yref_lemma_nested_singleton (x : αˡ → var) (v : αˡ → val) (t : αˡ → trm) H (Q : _ -> _ -> _) :
  shts.Forall (Disjoint ·.s ⟪l, {s}⟫) ->
  (∀ p : loc, H ∗ (p ~⟨i in ⟪l, {s}⟫⟩~> v i) ==>
    (hwp ⟪l, {s}⟫ (fun _ ↦ subst (x ⟨l,s⟩) p (t ⟨l,s⟩))
    (fun hv => (LGTM.wp shts fun hv' => Q hv hv' ∗ ∃ʰ (u : αˡ → val), p ~⟨i in ⟪l, {s}⟫⟩~> u i)))) →
  H ==> hwpgen_ref ⟪l, {s}⟫ x (fun i ↦ trm_val (v i)) t (fun hv => LGTM.wp shts (Q hv)) :=
by
  move=> ? imp; apply yref_lemma_nested=> // p;
  srw hhsingle bighstar_eq; apply hhimpl_trans
  { apply imp (p ⟨l,s⟩) }
  srw [2]hwp_labSet_single; apply hwp_conseq
  { move=> hv /=; apply hwp_conseq=> hv' /=
    ypull=> u; ysimp[u]
    srw hhsingle bighstar_eq //
    scase=> ?? /== ->-> }
  scase=> ?? /== ->->

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


macro "yref" p:term : tactic => do
  `(tactic|
  (yseq_xlet_if_needed; ystruct_if_needed;
   (first |
     apply yref_lemma_nested_singleton |
     apply yref_lemma_singleton |
     apply yref_lemma_nested |
     apply yref_lemma);
   { simp [disjE] }
   intro $p:term;
   try simp [$(mkIdent `subst):ident]))
macro "yifT" : tactic => do
  `(tactic|
  (yseq_xlet_if_needed; ystruct_if_needed; apply yif_lemma_true))

macro "yifF" : tactic => do
  `(tactic|
  (yseq_xlet_if_needed; ystruct_if_needed; apply yif_lemma_false))


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
  let thm <- do (match e with
    | .some thm => return thm
    | .none     => return mkIdent (<- pickHTripleLemma))
  {| eapply $thm:term |}

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
     rotate_right; (run_tac (do (<- Lean.Elab.Tactic.getMainGoal).setTag `yapp_goal)); yapp_simp; hide_mvars=>//'))

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

lemma trm_apps3 :
  trm_apps (trm_apps t1 t2) ts = trm_apps t1 (t2++ts) := by
  sorry

macro "ywp" : tactic =>
  `(tactic|
    (intros
     try simp_rw [Unary.trm_apps1]
     try simp_rw [Unary.trm_apps2]
     try simp_rw [trm_apps3]
     try (first | (
      apply ywp_lemma_fixs;
      { move=> ?; rfl }
      { intros; rfl }
      { sdone }
      { sdone }
      sdone)=> //'
                | (
      apply ywp_lemma_funs;
      { move=> ?; rfl }
      { rfl }
      { move=> ?; rfl; }
      sdone)=> //')
     try dsimp [Unary.isubst, List.mkAlist, AList.lookup, List.eraseP,List.dlookup]
     apply hwp_of_hwpgen
     all_goals try simp
       [hwpgen,
        subst,
        isubst, trm_apps, AList.lookup, List.dlookup]
     all_goals try simp [_root_.subst, trm_apps, Unary.isubst]))

macro "yunfold" : tactic =>
  `(tactic|
    (intros
     try simp_rw [Unary.trm_apps1]
     try simp_rw [Unary.trm_apps2]
     try simp_rw [trm_apps3]
     try (first | (
      apply ywp_lemma_fixs;
      { move=> ?; rfl }
      { intros; rfl }
      { sdone }
      { sdone }
      sdone)=> //'
                | (
      apply ywp_lemma_funs;
      { move=> ?; rfl }
      { rfl }
      { move=> ?; rfl; }
      sdone)=> //')
     try dsimp [Unary.isubst, List.mkAlist, AList.lookup, List.eraseP,List.dlookup]
    --  apply hwp_of_hwpgen
     all_goals try simp
       [hwpgen,
        subst,
        isubst, trm_apps, AList.lookup, List.dlookup]
     all_goals try simp [_root_.subst, trm_apps, Unary.isubst]))

macro "yval" : tactic => do
  `(tactic| (ystruct_if_needed; yseq_xlet_if_needed; (try ywp); apply yval_lemma))

macro "ystep" : tactic => do
  `(tactic| (ywp; yapp))

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

@[hhlocalE]
lemma hhlocal_pure : hhlocal s ⌜P⌝ = true :=
  by simp=> ? ![] ? -> //

@[hhlocalE]
lemma hhlocal_if (b : Prop) : hhlocal s (if b then P else Q) =
  if b then hhlocal s P else hhlocal s Q :=
  by scase_if

@[simp]
lemma cdot_set_mem (n : ℕ) (s : Set α) : (x ∈ (n • s)) = (x ∈ s ∧ n > 0) := sorry

/- ================================================================= -/
/- ====================== Tactics for Loops ======================== -/

lemma labSet_iUnion (s : Set β) (sᵢ : β -> Set α) :
  ⟪l, ⋃ i ∈ s, sᵢ i⟫ = ⋃ i ∈ s, ⟪l, sᵢ i⟫ := by sorry

instance RestrictToIndexNilUL (sᵢ : ℤ -> _) :
  RestrictToIndex z n [⟨⟪l, ⋃ i ∈ (Set.Ico z n), sᵢ i⟫, ht⟩] (fun i => [⟨⟪l, sᵢ i⟫, ht⟩]) := by
   srw labSet_iUnion; apply RestrictToIndexNilU

instance RestrictToIndexConsUL (sᵢ : ℤ -> _) [r:RestrictToIndex z n shts shtsᵢ] :
   RestrictToIndex z n (⟨⟪l, ⋃ i ∈ Set.Ico z n, sᵢ i⟫, ht⟩ :: shts) (fun i => (⟨⟪l,sᵢ i⟫, ht⟩ :: shtsᵢ i)) := by
  srw labSet_iUnion; apply RestrictToIndexConsU

instance RestrictToIndexNilU' (sᵢ : ℤ -> _) :
  RestrictToIndex z n [⟨⋃ i ∈ (Set.Ico z n), sᵢ i, ht⟩] (fun i => [⟨sᵢ i, ht⟩]) := by
  srw iUnion_eq_sum
  sdone

instance RestrictToIndexConsUL' (sᵢ : ℤ -> _) [r:RestrictToIndex z n shts shtsᵢ] :
   RestrictToIndex z n (⟨⟪l, ⋃ i ∈ Finset.Ico z n, sᵢ i⟫, ht⟩ :: shts) (fun i => (⟨⟪l,sᵢ i⟫, ht⟩ :: shtsᵢ i)) := by
  srw iUnion_eq_sum' -iUnion_eq_sum labSet_iUnion; apply RestrictToIndexConsU

instance RestrictToIndexNilU'' (sᵢ : ℤ -> _) :
  RestrictToIndex z n [⟨⟪l, ⋃ i ∈ (Finset.Ico z n), sᵢ i⟫, ht⟩] (fun i => [⟨⟪l, sᵢ i⟫, ht⟩]) := by
  srw iUnion_eq_sum' -iUnion_eq_sum; apply RestrictToIndexNilUL




/- Fisrt we provide instances for a typeclass which dirives
   [yfor_lemma] and [ywhile_lemma]   -/
set_option maxHeartbeats 1600000 in
lemma GenInstArr_eqSum (hv : hval α) (f : Int -> val)
  (op : hval α -> Int -> val) [PartialCommMonoid val]:
  (∀ i, PartialCommMonoid.valid (f i)) →
  (∀ i, PartialCommMonoid.valid (op hv i)) →
  hharrayFun s (fun i ↦ f i + op hv i) n x =
    hharrayFun s (fun x ↦ f x) n x +
    ∑ i ∈ ⟦(0 : ℤ) , n⟧, (x j + 1 + i.natAbs ~⟨j in s⟩~> op hv i) := by
  move=> ??; srw hharrayFun_hhadd_sum //'
  srw ?hharrayFun ?harrayFun; congr! 4=> ! [] /== //

lemma GenInstArr_eqGen (s : Set α) (x : α -> loc) (hv : Int -> hval α) (f : Int -> val) (n : ℕ)
  (op : hval α -> Int -> val) [PartialCommMonoid val] :
  (∀ i, PartialCommMonoid.valid (f i)) →
  (∀ i, PartialCommMonoid.valid (op (hv i) i)) →
  ∀ j ∈ ⟦(0 : ℤ) , n⟧,
    ∃ v H,
      PartialCommMonoid.valid v ∧
      hharrayFun s (fun x ↦ f x) n x + ∑ i ∈ ⟦0, j⟧,
       (x j + 1 + i.natAbs ~⟨j in s⟩~> op (hv i) i) =
        x i + 1 + j.natAbs ~⟨i in s⟩~> v ∗ H := by
  move=> ?? > /== ??; srw hharrayFun_hhadd_sum //'
  move: (harrayFun_chip_off (p := x) (n := n)
    (f := ((fun i ↦ if i < j then  f i + op (hv ↑i) ↑i else f i))) s j)=> h
  specialize h ?_ ?_=> //; scase: h=> H -> //
  move=> ⟨|⟨|⟨|//⟩⟩⟩ //


namespace AddPCM

instance GenInst (op : hval α -> Int -> Int) (x : α -> loc) :
  IsGeneralisedSum
    z n
    AddPCM.add AddPCM.valid
    (x i ~⟨i in s⟩~> 0)
    (fun i hv => x j ~⟨j in s⟩~> op hv i)
    (Int)
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> val.val_int (op hv i + j))
    (fun hv => x k ~⟨k in s⟩~> val.val_int (∑ i in ⟦z,n⟧, op hv i)) where
    eqGen := by
      move=> > ?
      exists (∑ i in ⟦z, j⟧, op (hv i) i) , emp
      srw sum_hhsingle; ysimp=> //
    eqInd := by srw hhadd_hhsingle //
    eqSum := by srw sum_hhsingle //

instance GenInstWithPure (op : hval α -> ℤ -> ℤ) (x : α -> loc) (P : hval α -> ℤ -> Prop) :
  IsGeneralisedSum
    z n
    AddPCM.add AddPCM.valid
    (x i ~⟨i in s⟩~> val_int 0)
    (fun i hv => x j ~⟨j in s⟩~> op hv i ∗ ⌜P hv i⌝)
    ℤ
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> val_int (op hv i + j) ∗ ⌜P hv (i)⌝)
    (fun hv => x k ~⟨k in s⟩~> val_int (∑ i in ⟦z,n⟧, op hv i) ∗ ⌜∀ j ∈ ⟦z,n⟧, P hv j⌝ ) where
    eqGen := by
      move=> > ?
      exists (∑ i in ⟦z, j⟧, op (hv i) i) , ⌜∀ k ∈ ⟦z,j⟧, P (hv k) k⌝
      srw sum_hhstar_hhpure hhstar_pure_hhadd -add_assoc -hhstar_pure_hhadd
      erw [sum_hhsingle]
    eqInd := by
      srw hhstar_pure_hhadd add_assoc add_comm add_assoc hhadd_hhsingle //
    eqSum := by srw sum_hhstar_hhpure [2]hhstar_pure_hhadd -add_assoc=> ?
                erw [sum_hhsingle]=> //

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

instance GenInstSum (op : hval α -> ℤ -> ℤ)
  (m : ℕ) (z n : ℤ) (x : α -> loc) (f : ℤ -> ℤ) (ini : ℤ -> ℤ) :
   IsGeneralisedSum
    z n
    AddPCM.add AddPCM.valid
    (hharrayFun s (ini ·) m x ∗ ⌜f ''⟦z, n⟧ ⊆ Set.Ico 0 m⌝)
    (fun i hv => x j + 1 + (f i).natAbs ~⟨j in s⟩~> op hv i)
    ℤ
    (fun k j => x i + 1 + (f k).natAbs ~⟨i in s⟩~> j)
    (fun i j hv => x k + 1 + (f i).natAbs ~⟨k in s⟩~> val.val_int (op hv i + j))
    (fun hv => ⌜f ''⟦z, n⟧ ⊆ Set.Ico 0 m⌝ ∗ hharrayFun s (ini ·) m x + (∑ i ∈ ⟦z, n⟧, (x j + 1 + (f i).natAbs ~⟨j in s⟩~> op hv i))) where
    eqGen := by sorry
    eqInd := by srw hhadd_hhsingle //'
    eqSum := by move=> hv; srw hhstar_pure_hhadd [3]add_comm add_assoc [2]add_comm -hhstar_pure_hhadd hhstar_comm

instance GenInstArrSum (op : ℤ -> hval α -> ℤ -> ℤ) (P : ℤ -> hval α -> ℤ -> Prop)
  (m : ℕ) (z n : ℤ) :
   IsGeneralisedSum
    z n
    AddPCM.add AddPCM.valid
    (hharrayFun s (fun _ => val_int 0) m x)
    (fun i hv => (∑ k ∈ ⟦0, m⟧, (x j + 1 + k.natAbs ~⟨j in s⟩~> op k hv i))
                 ∗ ⌜∀ k ∈ ⟦0, m⟧, P k hv i⌝ )
    (ℤ -> ℤ)
    (fun k f => hharrayFun s (f ·) m x)
    (fun i f hv => hharrayFun s (fun j => f j + op j hv i) m x ∗ ⌜∀ k ∈ ⟦0, m⟧, P k hv i⌝)
    (fun hv =>
      hharrayFun s (fun j => val_int (∑ i ∈ ⟦z, n⟧, op j hv i)) m x ∗
      ⌜∀ i ∈ ⟦z, n⟧, ∀ k ∈ ⟦0, m⟧, P k hv i⌝) where
    eqGen := by sorry
    eqInd := by sorry
    eqSum := by sorry

lemma arr_eq_sum (m : ℕ) (op : β -> ℤ)  (f : β -> ℤ) (fs : Finset β) (ini : ℤ -> ℤ):
  f '' fs ⊆ Set.Ico 0 m →
  hharrayFun s (ini ·) m x + (∑ i ∈ fs, (x j + 1 + (f i).natAbs ~⟨j in s⟩~> op i)) =
  hharrayFun s (fun id => val_int (ini id + ∑ i in { x ∈ fs | f x = id }, op i)) m x := by sorry

end AddPCM

namespace OrPCM

instance GenInst (op : hval α -> Int -> Bool) (x : α -> loc) :
  IsGeneralisedSum
    z n
    OrPCM.add OrPCM.valid
    (x i ~⟨i in s⟩~> false)
    (fun i hv => x j ~⟨j in s⟩~> op hv i)
    (Bool)
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> val.val_bool (op hv i || j))
    (fun hv => x k ~⟨k in s⟩~> val.val_bool (∃ i ∈ ⟦z,n⟧, op hv i)) where
    eqGen := by
      move=> > ?
      exists (∃ i ∈ ⟦z, j⟧, op (hv i) i) , emp
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

namespace AddRealPCM

instance GenInst (op : hval α -> ℤ -> ℝ) (x : α -> loc) :
  IsGeneralisedSum
    z n
    AddRealPCM.add AddRealPCM.valid
    (x i ~⟨i in s⟩~> val_real 0)
    (fun i hv => x j ~⟨j in s⟩~> op hv i)
    (ℝ)
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> val.val_real (op hv i + j))
    (fun hv => x k ~⟨k in s⟩~> val.val_real (∑ i in ⟦z,n⟧, op hv i)) where
    eqGen := by
      move=> > ?
      exists (∑ i in ⟦z, j⟧, op (hv i) i) , emp
      srw sum_hhsingle; ysimp=> //
    eqInd := by srw hhadd_hhsingle //
    eqSum := by srw sum_hhsingle //

instance GenInstWithPure (op : hval α -> ℤ -> ℝ) (x : α -> loc) (P : hval α -> ℤ -> Prop) :
  IsGeneralisedSum
    z n
    AddRealPCM.add AddRealPCM.valid
    (x i ~⟨i in s⟩~> val_real 0)
    (fun i hv => x j ~⟨j in s⟩~> op hv i ∗ ⌜P hv i⌝)
    (ℝ)
    (fun _ j =>  x i ~⟨i in s⟩~> j)
    (fun i j hv => x k ~⟨k in s⟩~> val.val_real (op hv i + j) ∗ ⌜P hv (i)⌝)
    (fun hv => x k ~⟨k in s⟩~> val.val_real (∑ i in ⟦z,n⟧, op hv i) ∗ ⌜∀ j ∈ ⟦z,n⟧, P hv j⌝ ) where
    eqGen := by
      move=> > ?
      exists (∑ i in ⟦z, j⟧, op (hv i) i) , ⌜∀ k ∈ ⟦z,j⟧, P (hv k) k⌝
      srw sum_hhstar_hhpure hhstar_pure_hhadd -add_assoc -hhstar_pure_hhadd
      srw sum_hhsingle
    eqInd := by
      srw hhstar_pure_hhadd add_assoc add_comm add_assoc hhadd_hhsingle //
    eqSum := by srw sum_hhstar_hhpure [2]hhstar_pure_hhadd -add_assoc sum_hhsingle //


@[simp]
lemma validE : PartialCommMonoid.valid = AddRealPCM.valid := by trivial

@[simp]
lemma addE : (· + ·) = AddRealPCM.add := by trivial

instance GenInstArr (op : hval α -> ℤ -> ℝ)
  (n : ℕ)
  (f : ℝ -> ℝ) (x : α -> loc) :
  IsGeneralisedSum
    0 n
    AddRealPCM.add AddRealPCM.valid
    (hharrayFun s (f ·) n x)
    (fun i hv => x j + 1 + i.natAbs ~⟨j in s⟩~> op hv i)
    (ℝ)
    (fun k j =>  x i + 1 + k.natAbs ~⟨i in s⟩~> j)
    (fun i j hv => x k + 1 + i.natAbs ~⟨k in s⟩~> val.val_real (op hv i + j))
    (fun hv => hharrayFun s (fun i => val.val_real $ f i + op hv i) n x) where
    eqGen := by
      move=> hv j jin; move: (GenInstArr_eqGen s x hv (f ·) n (op · ·))=> H
      specialize H ?_ ?_ j jin=> //; scase!: H=> [] //
    eqInd := by srw hhadd_hhsingle //'
    eqSum := by move=> hv; apply GenInstArr_eqSum hv (f ·) (op · ·)=> //

end AddRealPCM


lemma zlet_lemma_aux (shts : LGTM.SHTs αˡ) (ht₁ ht₂ : htrm αˡ) :
  Disjoint ⟪l, {s}⟫ shts.set ->
  LGTM.wp (⟨⟪l, {s}⟫, ht₁⟩ :: shts) (fun hv =>
    hwp ⟪l,{s}⟫ (fun i => subst x (hv ⟨l, s⟩) (ht₂ i)) (fun hv' =>
      Q (hv' ∪_⟪l,{s}⟫ hv) )) ==>
  LGTM.wp (⟨⟪l, {s}⟫, fun i => trm_let x (ht₁ i) (ht₂ i)⟩ :: shts) Q := by
  move=> ?
  srw [2]LGTM.wp_cons //=
  ychange hwp_let=> /=
  srw LGTM.wp_cons //=; apply hwp_conseq=> hv /=
  simp [fun_insert]
  srw LGTM.wp_Q_eq; rotate_right
  { move=> ?; srw LGTM.hwp_Q_eq=> hv
    srw fun_insert_ss' }
  apply hhimpl_trans; apply LGTM.wp_cons_last (sht := ⟨⟪l, {s}⟫, _⟩)=> //
  srw LGTM.wp_cons=> //=; srw hwp_labSet_single [2]hwp_labSet_single //

lemma zlet_lemma (H : hhProp αˡ) (shts : LGTM.SHTs αˡ) (ht₁ ht₂ : htrm αˡ) :
  Disjoint ⟪l, {s}⟫ shts.set ->
  H ==> LGTM.wp (⟨⟪l, {s}⟫, ht₁⟩ :: shts) (fun hv =>
    hwp ⟪l, {s}⟫ (fun i => subst x (hv ⟨l, s⟩) (ht₂ i)) (fun hv' =>
      Q (hv' ∪_⟪l, {s}⟫ hv) )) ->
  H ==>
    LGTM.wp (⟨⟪l, {s}⟫, fun i => trm_let x (ht₁ i) (ht₂ i)⟩ :: shts) Q := by
  move=> ??; ychange zlet_lemma_aux=> //

macro "zlet_if_needed" : tactic =>
  `(tactic| (try apply zlet_lemma;
                  ⟨solve | simp [disjE],
                    simp only [$(mkIdent `subst):ident, fun_insert]⟩))

macro "zseq_if_needed" : tactic =>
  `(tactic| (try apply zseq_lemma;
                  ⟨try solve | simp [disjE]=> //',
                    try simp only [$(mkIdent `subst):ident, fun_insert]⟩))

lemma zapp_lemma (H : hhProp α) :
  LGTM.triple shts H' Q' ->
    H ==> H' ∗ (Q' -∗ protect Q) ->
  H ==> LGTM.wp shts Q := by
  sorry

macro "zapp" e:term : tactic =>
  `(tactic| (
    zlet_if_needed;
    zseq_if_needed;
    apply zapp_lemma;
    eapply $e; rotate_right
    ysimp
    hide_mvars=> //'
  ))


declare_syntax_cat loop_op
declare_syntax_cat loop_arg
declare_syntax_cat loop_args
declare_syntax_cat loop_type


syntax "+" : loop_op
syntax "||" : loop_op
syntax "+." : loop_op
syntax ident : loop_op

syntax "(" ident ":=" term ")" : loop_arg
syntax loop_arg loop_args : loop_args

syntax "yfor" : loop_type
syntax "ywhile" : loop_type
syntax loop_type loop_op ? (term "," term) ? "with" (loop_arg colGe)* : tactic

macro_rules
  | `(tactic| yfor$loop_op with $[($x := $v)]*) => do
    let yforLemm <- `(
      yfor_lemma
        (z := _)
        (n := _)
        (add := $(mkIdent `add))
        (valid := $(mkIdent `valid)) $[ ( $x:ident := $v:term ) ]*)
    let tac <- `(tactic| (
      eapply $yforLemm; ⟨
      try solve | hsimp | ysimp,
      try simp , -- nonempty
      try simp [disjE]; try omega, -- s' ⊥ sᵢ
      try simp [disjE]; try omega, -- Pairwise disj
      omega, -- z <= n
      simp [hhlocalE], -- hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      simp [hhlocalE], -- ∀ hhlocal
      try solve | (simp=> > ??; (repeat move=>->); auto), -- Qeq
      try simp [LGTM.SHTs.set, $(mkIdent `subst):term]; try hsimp, -- step
      try hsimp, -- pre
      (move=> >; try hsimp; try simp [fun_insert])⟩ -- post
      ))
      match loop_op with
      | `(loop_op| ||) => `(tactic| open OrPCM      in $tac:tactic)
      | `(loop_op| +)  => `(tactic| open AddPCM     in $tac:tactic)
      | `(loop_op| +.) => `(tactic| open AddRealPCM in $tac:tactic)
      | `(loop_op| $i:ident) => `(tactic| open $i:ident in $tac:tactic)
      | _ => Macro.throwErrorAt loop_op "unsupported loop operation"

macro_rules
  | `(tactic| ywhile$loop_op $z:term, $n:term with $[($x := $v)]*) => do
    let ywhileLemma <- `(
      ywhile_lemma
        (z := $z)
        (n := $n)
        (add := $(mkIdent `add))
        (valid := $(mkIdent `valid)) $[ ( $x:ident := $v:term ) ]*)
    let tac <- `(tactic| (
      eapply $ywhileLemma; ⟨
        try solve | hsimp | ysimp,
        try simp , -- nonempty
        try simp [disjE]; try omega, -- s' ⊥ sᵢ
        try simp [disjE]; try omega, -- Pairwise disj
        omega, -- z <= n
        simp [hhlocalE], -- hhlocal
        simp [hhlocalE], -- ∀ hhlocal
        simp [hhlocalE], -- ∀ hhlocal
        simp [hhlocalE], -- ∀ hhlocal
        try solve | (simp=> > ??; (repeat move=>->); auto), -- Qeq

        try simp [LGTM.SHTs.set, $(mkIdent `subst):term]; try hsimp, -- step true
        try simp [LGTM.SHTs.set, $(mkIdent `subst):term]; try hsimp, -- step false
        skip, -- Cnd
        skip, -- Inv false
        try hsimp, -- pre
        (move=> >; try hsimp; try simp [fun_insert])⟩ -- post
      ))
      match loop_op with
      | `(loop_op| ||) => `(tactic| open OrPCM      in $tac:tactic)
      | `(loop_op| +)  => `(tactic| open AddPCM     in $tac:tactic)
      | `(loop_op| +.) => `(tactic| open AddRealPCM in $tac:tactic)
      | `(loop_op| $i:ident) => `(tactic| open $i:ident in $tac:tactic)
      | _ => Macro.throwErrorAt loop_op "unsupported loop operation"

@[simp]
lemma nonempty_labSet :
  ⟪n, s⟫.Nonempty = s.Nonempty := by sorry

/- ============ Tests for y-loops lemmas ============ -/
section

instance (priority := 0) : FindUniversal H emp H where
  univ := hempty
  H_eq := by hsimp
  Hu_eq := by hsimp


instance (priority := high) :
  FindUniversal (hharrayFun (@Set.univ α) f n (fun _ => p)) (hharrayFun Set.univ f n (fun _ => p)) emp where
  univ := harrayFun f n p
  H_eq := by hsimp
  Hu_eq := by rfl

instance (priority := high) :
  FindUniversal (α := α) ⊤ ⊤ emp where
  univ := htop
  H_eq := by hsimp
  Hu_eq := by move=> !h /== ⟨|⟩ // _ ? //


local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q
example (F : False) :
  LGTM.triple
    [⟨{11}, fun _ => (trm_for vr (val.val_int 1) (val.val_int 10) c).trm_seq c⟩ ,
     ⟨∑ i in ⟦1, 10⟧, {i}, ht⟩ ,
     ⟨∑ i in ⟦1, 10⟧, {-i}, ht⟩]
    ((x ⟨_ in {1}⟩|-> 0) ∗ R ∗↑ s)
    (fun hv => ((x ⟨_ in {11}⟩|->  ∑ j in ⟦0, 10⟧, (hv j))) ∗ R' ∗↑ s) := by
  yfor+ with
    (Inv := fun _ => emp)
    (Q := fun i hv => x ⟨_ in {11}⟩|-> (hv i + hv (-i)))
    (H₀ := x ⟨_ in {11}⟩|-> 0)
    (R := R)
    (R' := R')=> //

example (F : False) (n : ℕ) (f g : ℤ -> ℤ) :
  LGTM.triple
    [⟨{-2}, fun _ => (trm_for vr (val.val_int 0) (val.val_int n) c).trm_seq c⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {i}, ht⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {-1}, ht⟩]
    ((hharrayFun {-2} (f ·) n (fun _ => x)) ∗ R ∗↑ s)
    (fun hv => (hharrayFun {-2} (g ·) n (fun _ => x)) ∗ R' ∗↑ s) := by
  yfor+ with
    (Inv := fun _ => emp)
    (Q := (fun i hv => (x + 1 + i.natAbs) ⟨_ in {-2}⟩|-> hv i))
    (H₀ := hharrayFun {-2} (f ·) n (fun _ => x))
    (R := R)
    (R' := R')=> //


example (F : False) (n : ℕ) (f g h : ℤ -> ℤ) :
  LGTM.triple
    [⟨{-2}, fun _ => (trm_for vr (val.val_int 0) (val.val_int n) c).trm_seq c⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {i}, ht⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {-1}, ht⟩]
    ((hharrayFun {-2} (f ·) n (fun _ => x)) ∗ hharrayFun Set.univ (h ·) n (fun _ => p))
    (fun hv => (hharrayFun {-2} (g ·) n (fun _ => x)) ∗ hharrayFun Set.univ (h ·) n (fun _ => p)) := by
  yfor+ with
    (Inv := fun _ => emp)
    (Q := (fun i hv => (x + 1 + i.natAbs) ⟨_ in {-2}⟩|-> hv i))
    (H₀ := hharrayFun {-2} (f ·) n (fun _ => x))=> //

notation (priority := high+1) "⊤" => hhtop

example (F : False) (n : ℕ) (f g h : ℤ -> ℤ) :
  LGTM.triple
    [⟨{-2}, fun _ => (trm_for vr (val.val_int 0) (val.val_int n) c).trm_seq c⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {i}, ht⟩ ,
     ⟨∑ i in ⟦(0:ℤ) , n⟧, {-1}, ht⟩]
    ((hharrayFun {-2} (f ·) n (fun _ => x)) ∗ hharrayFun Set.univ (h ·) n (fun _ => p))
    (fun hv => (hharrayFun {-2} (g ·) n (fun _ => x)) ∗ ⊤) := by
  yfor+ with
    (Inv := fun _ => emp)
    (Q := (fun i hv => (x + 1 + i.natAbs) ⟨_ in {-2}⟩|-> hv i))
    (H₀ := hharrayFun {-2} (f ·) n (fun _ => x))=> //

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

example :
  emp ==>
    WP [1 | i in {(1 : ℤ) ,3} => let x := ⟨i⟩ in x + 1]
    { v, ⌜v ⟨1,1⟩ = 2 ∧ v ⟨2,1⟩ = 2 ∧ v ⟨1,3⟩ = 4⌝ } := by sorry

example (F : False) (H : hhProp Int)
  (h :
    hharrayFun {1} f n (fun _ => p) ==>
      hwp {1} g fun hv => ⌜ hv = fun _ => 0 ⌝ ∗ H ∗ hharrayFun {1} f n (fun _ => p)) :
  hharrayFun Set.univ f n (fun _ => p) ==>
    hwp {1} g Q := by
  yapp h=> //


instance : Coe (Labeled (ℤ × ℤ)) (ℤ × ℤ) where
  coe l := l.val

instance [s₁ : SubstTypeUniversal H₁ H₁'] [s₂ : SubstTypeUniversal H₂ H₂'] :
  SubstTypeUniversal (H₁ ∗ H₂) (H₁' ∗ H₂') where
  univ := s₁.univ ∗ s₂.univ
  Hα_eq := by srw s₁.Hα_eq s₂.Hα_eq bighstar_hhstar
  Hβ_eq := by srw s₁.Hβ_eq s₂.Hβ_eq bighstar_hhstar

instance :
  SubstTypeUniversal
    (hharrayFun (@Set.univ α) f n (fun _ => p))
    (hharrayFun (@Set.univ β) f n (fun _ => p))  where
  univ := harrayFun f n p
  Hα_eq := by rfl
  Hβ_eq := by rfl

instance : SubstTypeUniversal (α := α) (β := β) emp emp where
  univ := hempty
  Hα_eq := by hsimp
  Hβ_eq := by hsimp

instance : SubstTypeUniversal (α := α) (β := β) ⊤ ⊤ where
  univ := htop
  Hα_eq := by move=> !h /== ⟨|⟩ // _ ? //
  Hβ_eq := by move=> !h /== ⟨|⟩ // _ ? //

attribute [-simp] Set.singleton_prod

@[simp]
lemma labLift_eq (f : α -> β) :
  Function.labLift f ⟨l, x⟩ = ⟨l, f x⟩ := by rfl

@[simp]
lemma labLift_set (f : α -> β) (s : Set α) :
  Function.labLift f '' ⟪l, s⟫ = ⟪l, f '' s⟫ := by
  move=> ! [l x] /== ⟨[][l y] | ![] /== <- x ? <-⟩
  { simp => // }
  exists ⟨l, x⟩

@[simp]
lemma Prod.snd_img :
  (Prod.snd '' {s} ×ˢ s') = s' := by sby ext

lemma LGTM.wp_sht_eq (shts : SHTs α) :
  (shts.Forall₂ (fun sht sht'=> ∀ x ∈ sht.s, sht.s = sht'.s ∧ sht.ht x = sht'.ht x) shts') ->
  LGTM.wp shts Q = LGTM.wp shts' Q := by
  sorry

lemma feq [Nonempty α] (σ : α -> β) :
  x ∈ σ.labLift '' s ->
  σ (σ.labLift.invFunOn s x).val = x.val := by
  scase: x=> /= l v ?
  shave: σ.labLift (σ.labLift.invFunOn s ⟨l, v⟩) = ⟨l, v⟩
  { rw [Function.invFunOn_eq (f := σ.labLift)]=> // }
  simp  [Function.labLift]

macro "unify_hterm" σ:term : tactic =>  `(tactic| (
  rewrite [List.forall₂_cons]; rotate_left
  refine ⟨?_, ?_⟩; rotate_right
  dsimp; constructor
  { move=> ?? ⟨|⟩; exact Eq.refl _
    try rw [feq (σ := $σ)]=> //
    exact Eq.refl _ }
))


class IsLabSetUnion (s : Set αˡ) (l : outParam (List LabType)) (ss : outParam (List (Set α))) where
  eq : s = ⋃ i ∈ (l.zipWith (fun l s => ⟪l, s⟫) ss), i

instance : IsLabSetUnion (∅ : Set αˡ) [] [] where
  eq := by simp

instance : IsLabSetUnion ⟪l,s⟫ [l] [s] where
  eq := by simp

instance (s : Set αˡ) [inst: IsLabSetUnion s l ss] (l' : LabType) (s' : Set α) :
  IsLabSetUnion (⟪l', s'⟫ ∪ s) (l' :: l) (s' :: ss) where
  eq := by simp [<-inst.eq]

lemma InjOn_labSet :
  s.InjOn f -> ⟪l, s⟫.InjOn f.labLift := by
  move=> inj [] /== > <- ? [] > /== <- ? _ /inj //

lemma mem_zipWith (ls : List LabType) (x : Set αˡ) (ss : List $ Set α) :
  x ∈ (ls.zipWith (fun l s => ⟪l, s⟫) ss) -> ∃ᵉ (s ∈ ss) (l ∈ ls), x = ⟪l, s⟫ := by
  elim: ls ss=> // l ls /[swap] [] // s ss /(_ ss) /== /[swap] [-> //| xin /(_ xin)]
  move=> ![s ? l ? ->]; right; exists s=> ⟨//|⟩; right=> //

lemma IsLabSetUnion_inj (s : Set αˡ) (f : α -> β) [inst: IsLabSetUnion s ls ss] :
  ls.Nodup ->
  ss.Forall (Set.InjOn f) ->
  s.InjOn f.labLift := by
  srw inst.eq; elim: ls ss {inst}=> //== l ls ihls [] //== s ss ????
  erw [Set.injOn_union]=> /==
  { move=> ⟨|⟩; apply InjOn_labSet=> //
    move=> ⟨|⟩; apply ihls=> //
    scase=> ? a /= -> ? [m b] /= sl /mem_zipWith ![s ? m ?] -> /== // }
  move=> s /mem_zipWith ![s ? l ?] -> /==; simp [disjE]=> ⟨⟩ ? //

macro "ysubst" "with" "(" "σ" ":=" σ:term ")" : tactic =>
  let inj : Ident := mkIdent `inj
  `(tactic| (
    apply ysubst_lemma _ _ $σ; ⟨
      skip -- Hu ==> Qu
      ,simp -- shts.set.Nonempty
      ,simp [disjE] -- shts.Pairwise
      ,simp [hhlocalE] -- hhlocal H
      ,simp [hhlocalE] -- hhlocal Q
      ,(simp; apply IsLabSetUnion_inj=> //' /==) -- Set.InjOn
      , -- subst triple
      (simp [Function.comp]=> /=
       move=> $inj:ident
       simp (disch := solve | exact $inj | sby simp) [substE]
       srw LGTM.wp_sht_eq; rotate_left
       { repeat (unify_hterm $σ; hide_mvars)
         auto }
       clear $inj
       hsimp)
    ⟩))

example :
  hharrayFun (α := (ℤ×ℤ)ˡ) Set.univ f n (fun _ => p) ∗
  p ~⟪1, {(0 : ℤ)} ×ˢ {(1 : ℤ) ,3}⟫~> 0 ==>
    NWP [1 | i in {0} ×ˢ {(1 : ℤ) ,3} => let x := ⟨i.val.2⟩ in x + 1]
        [2 | i in {0} ×ˢ {1,3} => let x := ⟨i.val.2⟩ in x + 1]
    { v, ⌜v ⟨1,0,1⟩ = 2 ∧ v ⟨2,0,1⟩ = 2 ∧ v ⟨1,0,1⟩ = 4⌝ ∗ ⊤ } := by
  ysubst with (σ := Prod.snd); stop
  apply ysubst_lemma _ _ Prod.snd
  { ysimp }
  { simp }
  { simp [disjE] }
  { simp [hhlocalE] }
  { simp [hhlocalE] }
  { simp; apply IsLabSetUnion_inj=> //' /== }
  { simp [Function.comp]=> /=
    move=> inj
    simp (disch := solve | exact inj | sby simp) [substE]
    srw LGTM.wp_sht_eq; rotate_left
    { repeat (unify_hterm Prod.snd; hide_mvars)
      auto }
    clear inj }

attribute [disjE] Set.subset_diff

macro "ymerge" l:num "with" "(" "μ" ":=" μ:term ")" : tactic =>
  `(tactic| (
    eapply ymerge_lemma $μ (shts := _) (l := $l) (ind := $l - 1) (H := _) (Q' := _) (ex := (by dsimp only [FindUniversal.univ]; refine inferInstance)); ⟨
      rfl -- sht[is]
      ,simp -- t.Nonempty
      ,try dsimp; try auto -- ht
      ,skip -- sub
      ,simp [disjE] -- Pairwise disj
      ,simp --shts.set.Nonempty
      ,ysimp -- hhimpl univ
      ,simp [hhlocalE,disjE] -- hhlocal H
      ,simp [hhlocalE,disjE] -- hhlocal Q
      ,try dsimp -- triple
      ,skip
      ,skip
      ,try dsimp=> //' -- indL
    ⟩))

example : hharrayFun (α := (ℤ×ℤ)ˡ) Set.univ f n (fun _ => p) ∗
  p ~⟪1, {(0 : ℤ)} ×ˢ {(1 : ℤ) ,3}⟫~> 0 ==>
    NWP [1 | i in {0} ×ˢ {(1 : ℤ) ,3} => let x := ⟨i.val.2⟩ in x + 1]
        [2 | i in Set.Ico 1 5 ×ˢ {1,3} => let x := ⟨i.val.2⟩ in x + 1]
    { v, ⌜v ⟨1,0,1⟩ = 2 ∧ v ⟨2,0,1⟩ = 2 ∧ v ⟨1,0,1⟩ = 4⌝ ∗ ⊤ } := by
  ymerge 2 with (μ := fun x => ⟨1, x.2⟩)
  { sorry }
  sorry

end
