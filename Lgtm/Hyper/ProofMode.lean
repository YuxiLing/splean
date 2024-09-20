import Lean
-- lemmas on heaps
import Mathlib.Data.Finmap
import Qq

import Lgtm.Unary.Util
import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.Subst
import Lgtm.Hyper.Arrays
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

@[app_unexpander hwp] def unexpandHWP : Lean.PrettyPrinter.Unexpander
  | `($(_) ⟪$n:num,$s⟫ (fun $i:ident => [lang|$t])) => `(WP [$n| $i in $s => $t] ⋯)
  | _ => throw ( )

-- #check LGTM.SHT.mk
macro_rules
  | `([sht| [$n | $i in $s => $t] ]) => `(LGTM.SHT.mk ⟪$n, $s⟫ (fun $i:ident => [lang|$t]))

@[app_unexpander LGTM.SHT.mk] def unexpandSHT : Lean.PrettyPrinter.Unexpander :=
  fun x => match x with
  | `($(_) ⟪$n:num,$s⟫ fun $i:ident => [lang|$t]) => `([sht| [$n | $i in $s => $t] ])
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
  | `($(_) ⟪$n:num,$s⟫ $f $_) =>
    match f with
    | `(fun $i:ident => [lang|$t]) => `(WP [$n| $i in $s => $t] ⋯)
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

-- class FindLabel (l : LabType) (sht : LGTM.SHTs (Labeled α)) (i : outParam ℕ)
--   (_ : outParam (i < sht.length)) where
--   findLabel : ∃ s, sht[i].s = ⟪l, s⟫

-- instance (priority := high) FindLabelHead : FindLabel l (⟨⟪l,s⟫, ht⟩ :: shts) 0 (by simp) where
--   findLabel := by move=> ⟨|⟩//

-- instance FindLabelTail (shts : LGTM.SHTs (Labeled α)) (pi : i < shts.length)
--   [inst: FindLabel l shts i pi] :
--   FindLabel l (⟨⟪l',s⟫, ht⟩ :: shts) (i+1) (by simp; omega) where
--   findLabel := by scase: inst=> [s] /== ->; exists s=> //

lemma xfocus_lemma (l : LabType) (shts : LGTM.SHTs (Labeled α)) {pi : l-1 < shts.length} :
  (List.Pairwise (Disjoint ·.s ·.s) shts) ->
  LGTM.wp shts Q = hwp shts[l-1].s shts[l-1].ht fun hv => LGTM.wp (shts.eraseIdx (l-1)) (Q $ hv ∪_shts[l-1].s ·) := by
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

lemma xunfocus_lemma (l : LabType) (shts : LGTM.SHTs (Labeled α)) {pi : l-1 < shts.length}
  (Q' : hval (Labeled α) -> hval (Labeled α) -> hhProp (Labeled α)):
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (shts.Forall (Disjoint ⟪l,s⟫ ·.s)) ->
  (∀ hv hv', Q' hv hv' = Q (hv ∪_⟪l, s⟫ hv')) ->
  hwp ⟪l,s⟫ ht (fun hv => LGTM.wp shts fun hv' => Q' hv hv') =
  LGTM.wp (shts.insertNth (l-1) ⟨⟪l, s⟫, ht⟩) Q := by
  move=> dj dj' Qeq; srw (xfocus_lemma l)
  { srw List.getElem_insertNth_self //= List.eraseIdx_insertNth /=
    congr! 4=> //' }
  srw List.pairwise_iff_getElem at dj
  srw List.forall_iff_forall_mem at dj'
  srw List.pairwise_iff_getElem=> > ?
  srw ?(List.insertNth_getElem shts) //'
  { scase: [i < l - 1]=> ?
    { srw dif_neg //' [2]dif_neg; rotate_left; omega
      scase: [i = l-1]=> [?|?]
      { srw dif_neg //' dif_neg; rotate_left; omega
        apply dj; omega }
      srw dif_pos //' /= dif_neg; rotate_left; omega
      apply dj'; apply List.getElem_mem }
    srw dif_pos //';  scase: [j < l-1]=> [?|?]
    { srw dif_neg //'; scase: [j = l-1]=> ?
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
lemma xfocus_set_lemma_aux (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) {pi : l-1 < shts.length} :
  shts[l-1].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts (l - 1))) ⟪l, Set.univ⟫) ->
    (hwp ⟪l, s \ s'⟫ shts[l-1].ht fun hv =>
    LGTM.wp ((shts.eraseIdx (l-1)).insertNth (l-1) ⟨⟪l, s ∩ s'⟫,shts[l-1].ht⟩) fun hv' =>
      Q $ fun_lab_insert l (hv' ∪_⟪l,s'⟫ hv) hv') ==> LGTM.wp shts Q := by
    move=> seq /[dup]?/List.pairwise_iff_getElem dj' /[dup] dj₁ /Set.disjoint_left dj
    srw (xfocus_lemma l) //' seq -(Set.diff_union_inter ⟪l,s⟫ ⟪l,s'⟫) /==
    srw hwp_union; apply hwp_conseq=> //'; rotate_left
    { simp [disjE, Set.disjoint_sdiff_inter] }
    move=> hv₁ /=; srw (xfocus_lemma l)
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
    { scase: [i < l - 1]=> ?
      { srw dif_neg //'; scase: [i = l -1]=> ?
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
      scase: [j < l - 1]=> ?
      { srw dif_neg //'; scase: [j = l - 1]=> ?
        { srw dif_neg //' (List.eraseIdx_getElem _) //' dif_neg //'
          apply dj'=> //' }
        srw dif_pos //'=> /=; apply Set.disjoint_of_subset _ _ dj₁=> x //'
        srw shts_set_eq_sum /== => ?; exists (i)=> ⟨|⟩
        { srw List.length_eraseIdx=> //' }
        srw getElem!_pos //'  (List.eraseIdx_getElem _) //' }
      srw dif_pos //'(List.eraseIdx_getElem _) //' }
    all_goals srw List.length_eraseIdx=> //'

lemma xfocus_set_lemma (l : LabType) (s' s : Set α) (shts : LGTM.SHTs (Labeled α)) {pi : l-1 < shts.length} :
  shts[l-1].s = ⟪l, s⟫ ->
  (shts.Pairwise (Disjoint ·.s ·.s)) ->
  (Disjoint (LGTM.SHTs.set (List.eraseIdx shts (l - 1))) ⟪l, Set.univ⟫) ->
    H ==> (hwp ⟪l, s \ s'⟫ shts[l-1].ht fun hv =>
    LGTM.wp ((shts.eraseIdx (l-1)).insertNth (l-1) ⟨⟪l, s ∩ s'⟫,shts[l-1].ht⟩) fun hv' =>
      Q $ fun_lab_insert l (hv' ∪_⟪l,s'⟫ hv) hv') -> H ==> LGTM.wp shts Q := by
  move=> *; apply hhimpl_trans_r; apply xfocus_set_lemma_aux=> //


open Lean Elab Tactic Meta Qq

attribute [-simp] fun_insert
macro "xfocus" n:num : tactic => do
  `(tactic| (erw [xfocus_lemma $n:term]=> /=; ⟨skip, simp, try simp [disjE]⟩))

macro "xfocus" n:num ", " s:term : tactic => do
  `(tactic| (apply xfocus_set_lemma $n:term $s=> /=;
             ⟨try simp [disjE], try simp [disjE], skip, try auto⟩
   ))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xunfocus" : tactic => do
  {| srw xunfocus_lemma /== |}
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


instance (α : Type*) : Coe (Labeled α) α where
  coe l := l.val

section

variable {H : hhProp (Labeled Int)}


#check [sht| [1 | i in {1,3} => let x := ⟨i.val⟩ in x + 1] ]
example :
  H ∗ H ==>
    NWP [1 | i in {1,3} => let x := ⟨i⟩ in x + 1]
        [2 | i in {1,3} => let x := ⟨i⟩ in x + 1]
    { v, ⌜v ⟨1,1⟩ = 2 ∧ v ⟨2,1⟩ = 2 ∧ v ⟨1,1⟩ = 2⌝ } := by
  xfocus 1; xunfocus
  xfocus 2, {3}=> /==
  sorry
#check
  { (H ∗ H) }
    [1 | i in {1,3} => let x := ⟨i⟩ in x + 1]
    [2 | i in {1,3} => let x := ⟨i⟩ in x + 1]
  { v, ⌜v ⟨1,1⟩ = 2 ∧ v ⟨1,1⟩ = 2 ∧ v ⟨1,1⟩ = 2⌝ }

end
