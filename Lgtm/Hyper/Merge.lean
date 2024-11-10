-- import Ssreflect.Lang
import Mathlib.Data.Finmap

-- lemmas about big operators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

import Lgtm.Common.Util
import Lgtm.Common.LabType

import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog
import Lgtm.Unary.ArraysFun

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.WP
import Lgtm.Hyper.WPUtil
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Subst.YLemmas

open Classical val trm

section
variable {α : Type} (s : Set α) (σ : α -> β)

def hevalExact (s : Set α) (hh : hheap α) (ht : htrm α) (hQ : hval α -> hhProp α) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    hevalExact_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv')
    /-                    hQ'                      ==>         hQ -/

lemma heval_imp_hevalExact :
  heval s hh ht hQ ->
  hevalExact s hh ht hQ := by
  move=> [hQ'] [hev₁ hev₂]
  exists (fun a ↦ sP' (hh a) (ht a))=> ⟨|⟩
  { simp [hevalExact_nonrel]=> > ha
    apply evalExact_sP'
    sby move: (hev₁ a) ha=> /[apply] /eval_imp_exact [>] /evalExact_sP' }
  move=> >
  apply hhimpl_trans_r
  apply (hev₂ hv)=> /=
  apply bighstarDef_himpl=> > ha hh'
  specialize (hev₁ a ha)
  sby apply sP'_strongest in hev₁=> /[apply]

lemma hevalExactNR_imp_hevalNR :
  hevalExact_nonrel s hh ht hQ ->
  heval_nonrel s hh ht hQ := by
  sby unfold hevalExact_nonrel heval_nonrel=> hex > /hex /exact_imp_eval

lemma hevalExactNR_validSubst (hh' : hheap α) (hv : hval α) :
  hevalExact_nonrel (ssubst σ s s) hh ht hQ ->
  (∀ a ∈ s, hQ (σ a) (hv a) (hh' a)) ->
  validSubst σ s hh' := by
  move=> evex hQH a ain b bin σE
  move: (evex (σ a)); srw fsubst_inE /== => /(_ (ain)) /(_ (Eq.refl (σ a)))
  move=> /evalExact_det /(_ (hQH _ ain)) /σE /(_ (hQH _ bin)) //

lemma hevalExactNR_validSubst_val (hh' : hheap α) (hv : hval α) :
  hevalExact_nonrel (ssubst σ s s) hh ht hQ ->
  (∀ a ∈ s, hQ (σ a) (hv a) (hh' a)) ->
  validSubst σ s hv := by
  move=> evex hQH a ain b bin σE
  move: (evex (σ a)); srw fsubst_inE /== => /(_ (ain)) /(_ (Eq.refl (σ a)))
  move=> /evalExact_det /(_ (hQH _ ain)) /σE /(_ (hQH _ bin)) //

set_option maxHeartbeats 800000 in
lemma heval_hsubst_merge :
  validSubst σ s hh ->
  (∀ hv h, Q hv h -> ∀ a ∉ s, h a = hh a) ->
  heval (ssubst σ s s) (fsubst σ s hh) ht (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  heval s hh (ht ∘ σ) Q := by
  move=> vs Ql /heval_imp_hevalExact ![hQ /[dup] /hevalExactNR_imp_hevalNR evex ev himp]
  exists hQ ∘ σ; constructor
  { apply fsubst_heval_nonrel=> //
    apply heval_nonrel_conseq=> // ??
    sby srw fsubst_comp_σ }
  move=> hv /= h hQh
  shave ?: ∀ a ∈ s, hQ (σ a) (hv a) (h a)
  { move=> a ain; move: (hQh a); srw if_pos // }
  move: (himp (fsubst σ s hv) (fsubst σ s h))
  shave H: bighstarDef (ssubst σ s s) (fun a ↦ hQ a (fsubst σ s hv a)) (fsubst σ s hh) (fsubst σ s h)
  { move=> a; scase_if
    { move=>/fsubst_inE /== a' ? <-
      move: (hQh a'); srw if_pos //= ?fsubst_σ //
      { apply hevalExactNR_validSubst (hv := hv)=> // }
      { apply hevalExactNR_validSubst_val (hv := hv)=> // } }
    sby move=> ?; srw ?fsubst_out }
  move=> /(_ H) ![hv' h' /=] /fsubst_eq_local_eq heq hQ vs'
  let f := fun a => if σ a ∈ ssubst σ s s then fsubst σ s hv (σ a) else hv' (σ a)
  exists f=> /=
  shave->: (hv ∪_s f) = (fsubst σ s hv ∪_(ssubst σ s s) hv') ∘ σ
  { move=> !a /=; scase_if=> ain //
    srw if_pos // ?fsubst_σ //;
    { apply hevalExactNR_validSubst_val (hv := hv)=> // }
    apply fsubst_in=> // }
  shave-> //: h = h'
  move=> !a; scase: [a ∈ s]=> [|/heq//]
  { move: (hQh a) hQ; scase_if=> // ? -> /Ql // }
  sapply=> //
  apply hevalExactNR_validSubst (hv := hv)=> //;

lemma htriple_merge :
  H ==> validSubst σ s ->
  (∀ hv, hhlocal s (Q hv)) ->
  hhlocal s H ->
  htriple (ssubst σ s s) ht (hsubst σ s H) (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  htriple s (ht ∘ σ) H Q := by
  move=> vs Ql Hl htr ? /[dup] Hh /vs ?; apply heval_hsubst_merge=> //
  { move=> > /Ql /[swap] ? /[swap] ? -> //; srw (Hl _ Hh) // }
  apply htr=> ⟨|⟩ //

-- lemma triple_merge :
--   H ==> validSubst σ s ->
--   (∀ hv, hhlocal s (Q hv)) ->
--   hhlocal s H ->
--   htriple (ssubst σ s s) ht (hsubst σ s H) (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
--   LGTM.triple s (ht ∘ σ) H Q := by
--   move=> vs Ql Hl htr ? /[dup] Hh /vs ?; apply heval_hsubst_merge=> //
--   { move=> > /Ql /[swap] ? /[swap] ? -> //; srw (Hl _ Hh) // }
--   apply htr=> ⟨|⟩ //


end

section

class HPropExact (H : hProp) where
  isExact : ∀ h₁ h₂, H h₁ -> H h₂ -> h₁ = h₂


lemma validSubst_union_fun (h₁ h₂ : hheap α) :
  validSubst σ s₁ h₁ ->
  validSubst σ s₂ h₂ ->
  hlocal s₁ h₁ ->
  hlocal s₂ h₂ ->
  Disjoint s₁ s₂ ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  validSubst σ (s₁ ∪ s₂) (h₁ ∪ h₂) := by
  move=> vs₁ vs₂ h₁l h₂l dj σD a /== [] ain b []bin
  { move=> /vs₁-> //; srw ?h₂l // }
  { move=> /σD // }
  { move=> /(@Eq.symm _ _ _) /σD // }
  move=> /vs₂-> //; srw ?h₁l //

instance : HPropExact hempty := ⟨by move=> ?? ->->⟩
instance [inst₁ : HPropExact H₁] [inst₂ : HPropExact H₂] : HPropExact (H₁ ∗ H₂) := ⟨
  by move=> > ![>] /inst₁.isExact ex₁ /inst₂.isExact ex₂ ? -> ![>] /ex₁->/ex₂ //⟩

instance : HPropExact (harrayFun N p f) := ⟨sorry⟩

-- lemma htriple_extend_univ' (Q : hval α -> hhProp α) (H' H'' : hProp) :
--   himpl H' H'' ->
--   s.Nonempty ->
--   hhlocal s H ->
--   (∀ (hv : hval α), hhlocal s (Q hv)) ->
--   htriple s t (H ∗ [∗ in Set.univ | H']) (Q ∗ [∗ in @Set.univ α | H'']) =
--   htriple s t (H ∗ [∗ in s| H']) (Q ∗ [∗ in s| H'']) := by
--   move=> imp
--   scase: [∃ h, H' h]=> /==
--   { move=> unsat [a ain] * ⟨|⟩ ?? ![] >? /(_ a); srw if_pos// }
--   move=> h ? _ ??
--   srw (bighstarDef_univ_split (s := s))
--   srw -[2](htriple_frame_in (H' := [∗ in sᶜ| H']) (s' := sᶜ))=> //
--   { congr! 1=> [|!hv /=] <;> ysimp <;> ysimp
--      }
--   { exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a ↦ a }
--   exists (fun a => if a ∉ s then h else ∅)=> a /=
--   scase: [a ∈ sᶜ]=> /== //


variable {α : Type} (μ : α -> α) {shts : LGTM.SHTs αˡ}
variable {ind : ℕ} {indL : ind < shts.length} (l : ℕ) (t : Set α) {ht : htrm αˡ}
-- variable {cancel : ∀ a ∈ μ '' t, μ a = a }
variable {μ_img : μ '' t ⊆ t}
variable {shts_ind : shts[ind] = ⟨⟪l, t⟫, ht⟩}
variable {shts_disj : shts.Pairwise (Disjoint ·.s ·.s)}
-- variable {labDisj : ⟪l, t⟫ ⊆ shts.set}
variable {labDisj : ∀ ind' (h : ind' < shts.length), ind ≠ ind' -> ⟪l, t⟫ ∩ shts[ind'].s = ∅}
variable {htEq : (∀ x ∈ t, ht ⟨l,x⟩ = ht ⟨l,(μ x)⟩)}

@[simp]
noncomputable def Function.liftLab : αˡ -> αˡ := fun ⟨l', x⟩ => if l' = l ∧ x ∈ t then ⟨l, μ x⟩ else ⟨l', x⟩

include htEq labDisj labDisj shts_ind indL μ_img shts_disj

attribute [-simp] Set.eqOn_union

private lemma shts_htrm_μ :
  shts.set.EqOn shts.htrm (shts.htrm ∘ (μ.liftLab l t)) := by
  elim: shts ind=> //= sht shts ihShts /== dj dj'; scase=> /==
  { move=> -> /== ? [l' x] ? /==; scase_if=> /==
    move=> ??; srw if_pos //; apply μ_img=> // }
  move=> ind ? ? lD
  simp [Set.eqOn_union]=> ⟨|⟩
  { move=> [l' x] xin; move: (lD 0)=> /== /Set.eq_empty_iff_forall_not_mem /== int
    srw [-2 1]if_neg //; move: (int ⟨l', x⟩)=> /== /(_ xin) /== }
  move=> x xin; simp [fun_insert, -Function.liftLab]
  srw ?if_neg
  { apply ihShts=> //' ind' ??; move: (lD (ind' + 1))=> // }
  { scase: x=> /== l' x; scase_if=> /== //'
    { move: (lD 0)=> /== /Set.eq_empty_iff_forall_not_mem lD /[dup] leq
      move: (lD ⟨l', μ x⟩)=> /==/[apply] In ??; srw -leq; apply In
      apply μ_img=> // }
    move=> ? /shts_set_eqSum /== sht /dj /Set.disjoint_left /[apply] // }
  move: xin=> /shts_set_eqSum /== sht /dj /Set.disjoint_left /[apply] //

attribute [-simp] Function.liftLab in
omit htEq μ_img shts_disj in
set_option maxHeartbeats 800000 in
private lemma shts_set_set :
  LGTM.SHTs.set ((List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩).set ind ⟨⟪l, μ '' t⟫, ht⟩) =
  ssubst (μ.liftLab l t) shts.set shts.set := by
  elim: shts ind=> /== sht shts ihShts []
  { simp=> -> /= lD ! [l' x] /== ⟨[]|⟩/==
    { move=> -> y ? <-; srw fsubst_inE /==;
      exists ⟨l, y⟩; simp [Function.liftLab]=> ⟨|⟩ // }
    { move=> /shts_set_eqSum /== sht /List.mem_iff_getElem /== ind' indL <- ?
      move: (lD (ind' + 1))=> /== /(_ indL) /Set.eq_empty_iff_forall_not_mem lD
      srw fsubst_inE /==; exists ⟨l', x⟩=> /== ⟨|⟩
      { right; srw shts_set_eqSum /==; exists shts[ind']=> ⟨|⟩ //
        srw List.mem_iff_getElem=> // }
      simp [Function.liftLab]; move: (lD ⟨l', x⟩)=> /== // }
    srw fsubst_inE=> /== [l' x] /= [] /==
    { move=> -> xin; simp [Function.liftLab, xin]=> <-<- // }
    move=> /shts_set_eqSum /== sht /List.mem_iff_getElem /== ind' indL <- ?
    move: (lD (ind' + 1))=> /== /(_ indL) /Set.eq_empty_iff_forall_not_mem lD
    simp [Function.liftLab]; srw if_neg=> /==
    { move=> <- <-; right; srw shts_set_eqSum /==; exists shts[ind']=> ⟨|⟩ //
      srw List.mem_iff_getElem=> // }
    move: (lD ⟨l', x⟩)=> /== // }
  move=> ind /== indL ? lD; srw ihShts //
  { move=> ! [l' x] /== ⟨[]|⟩
    { move: (lD 0)=> /== /Set.eq_empty_iff_forall_not_mem lD In
      srw fsubst_inE; exists ⟨l', x⟩=> /== ⟨|⟩ //
      simp [Function.liftLab]; move: (lD ⟨l',x⟩)=> /== // }
    srw ?fsubst_inE=> /==
    { move=> x *; exists x=> // }
    move=> [l' x] [In <-|??]
    { left; simp [Function.liftLab]; srw if_neg //
      move: (lD 0)=> /== /Set.eq_empty_iff_forall_not_mem /(_ (Labeled.mk l' x)) // }
    right; exists ⟨l', x⟩=> // }
  move=> ind; move: (lD (ind + 1))=> //

omit indL shts_ind shts_disj labDisj htEq in
private lemma validSubst_out :
  hlocal (shts.set \ ⟪l, t⟫) h ->
  validSubst (Function.liftLab μ l t) shts.set h := by
  move=> hl a ain b bin
  scase: [a ∈ ⟪l,t⟫]=> ain
  { scase: [b ∈ ⟪l,t⟫]=> bin
    { srw /== ?if_neg // }
    srw /== if_neg ?if_pos //==
    move: ain bin=> /== H ? /[swap] /H /[swap] ? /[swap] -> H;
    exfalso; move: H=> /==; apply μ_img=> // }
  scase: [b ∈ ⟪l,t⟫]=> bin
  { srw /== if_pos ?if_neg //==
    move: bin ain=> /== H ? /[swap] /(@Eq.symm _ _ _) /H /[swap] ? /[swap] <- H;
    exfalso; move: H=> /==; apply μ_img=> // }
  srw ?hl //

omit indL shts_ind shts_disj labDisj htEq in
private lemma fsubst_id :
  hlocal (shts.set \ ⟪l, t⟫) h ->
  fsubst (Function.liftLab μ l t) shts.set h = h := by
  move=> hl ! [l' x]
  srw fsubst partialInvSet;
  scase: [∃ a ∈ shts.set, Function.liftLab μ l t a = ⟨l',x⟩]=> H
  { srw dif_neg //== hl // => In; move: H=> /==
    exists ⟨l', x⟩=> ⟨//|⟩; srw if_neg // }
  srw (dif_pos H) /=
  move: (choose_spec H)
  move: (choose H)=> a
  scase: [a ∈ ⟪l, t⟫]=> ?
  { scase=> ? /==; srw if_neg // }
  move=> [?] /==; srw if_pos //== => <- <-; srw ?hl //== => ?
  apply μ_img; exists a.val=> //


omit indL shts_ind shts_disj labDisj htEq in
private lemma hsubst_id :
  hhlocal (shts.set \ ⟪l, t⟫) H ->
  hsubst (Function.liftLab μ l t) shts.set H = H := by
  move=> hl !h !⟨![h -> ??]|?⟩
  { srw fsubst_id // }
  exists h=> ⟨|⟨//|⟩⟩
  { srw fsubst_id // }
  sby apply validSubst_out

omit μ_img shts_disj labDisj htEq in
@[local simp] lemma shtsE : shts.set \ ⟪l, t⟫ ∪ ⟪l, t⟫ = shts.set := by
  srw Set.diff_union_of_subset shts_set_eqSum=> ?? /==; exists shts[ind]=> ⟨|⟩
  { srw List.mem_iff_getElem=> // }
  sby srw shts_ind

omit shts_disj labDisj htEq in
set_option maxHeartbeats 800000 in
private lemma hsubstE :
  hhlocal (shts.set \ ⟪l, t⟫) H₁ ->
  hsubst (Function.liftLab μ l t) shts.set (H₁ ∗ [∗ in ⟪l, t⟫| H₂]) =
  H₁ ∗ [∗ in ⟪l, μ '' t⟫| H₂] := by
  move=> ?;
  shave μP : ∀ a ∈ ⟪l, t⟫, ∀ a' ∉ ⟪l, t⟫, Function.liftLab μ l t a ≠ Function.liftLab μ l t a'
  { move=> b ? [??] ain *; simp [Function.liftLab]; srw if_pos ?if_neg //
    move: ain => /== /[swap] <- /== /[swap] <- /==; apply μ_img=> //; exists b.val=> // }
  srw -(hsubst_hhstar (s₁ := shts.set \ ⟪l, t⟫) (s₂ := ⟪l, t⟫)) //'
  { srw hsubst_id //' (hsubst_bighstar (H := fun _ => H₂)) //'
    { congr! => ! [m x]; srw fsubst_inE
      { srw (Set.inter_eq_right.mpr)
        { move=> ⟨|⟩ /==
          { move=> [n y] /= -> In; simp [In]=> // }
          move=> -> x ? <-; exists ⟨l, x⟩=> // }
        srw shts_set_eqSum=> ?? /==; exists shts[ind]=> ⟨|⟩
        { srw List.mem_iff_getElem=> // }
        sby srw shts_ind }
      move=> a /[swap] b ??
      scase: [a ∈ ⟪l, t⟫]
      { move=> /[dup]/Set.mem_def ? /μP H /(@Eq.symm _ _ _) /H /Set.mem_def // }
      move=> /[dup]/Set.mem_def ? /μP /[apply] /Set.mem_def // }
    { srw shts_set_eqSum=> ?? /==; exists shts[ind]=> ⟨|⟩
      { srw List.mem_iff_getElem=> // }
      sby srw shts_ind }
    move=> a /[swap] b ??
    scase: [a ∈ ⟪l, t⟫]
    { move=> /[dup]/Set.mem_def ? /μP H /(@Eq.symm _ _ _) /H /Set.mem_def // }
    move=> /[dup]/Set.mem_def ? /μP /[apply] /Set.mem_def // }
  { srw shtsE // }
  { exact Set.disjoint_sdiff_left }
  move=> ? ain [? b] *; simp [Function.liftLab]; srw if_neg ?if_pos //
  move: ain => /== ? /[apply] /[swap] -> /==; apply μ_img=> //; exists b=> //;

omit indL shts_ind shts_disj labDisj htEq in
private lemma μsub : ⟪l, μ '' t⟫ ⊆ ⟪l, t⟫ := by
  move=> ?; simp [-Set.mem_image]=> ? /μ_img //

omit indL shts_ind shts_disj labDisj htEq in
private lemma disjμ : Disjoint (shts.set \ ⟪l, t⟫) ⟪l, μ '' t⟫ := by
  apply Set.disjoint_of_subset; apply subset_refl; rotate_left
  { exact Set.disjoint_sdiff_left }
  apply μsub=> //

omit μ_img shts_disj htEq in
private lemma set_set :
  LGTM.SHTs.set (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩) =
  ssubst (Function.liftLab μ l t) shts.set shts.set := by
  srw -shts_set_set //'

-- omit μ_img shts_disj htEq in
set_option maxHeartbeats 800000 in
attribute [-simp] Set.mem_image labSet_mem in
omit htEq in
private lemma set_htrm :
  (LGTM.SHTs.set (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩)).EqOn
  shts.htrm (LGTM.SHTs.htrm (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩)) := by
  elim: shts ind=> //== sht shts ihShts dj ? []
  { simp=> -> /= lD ? /== [?|]
    { srw ?if_pos //; apply μsub=> // }
    srw shts_set_eqSum=> /== ? /List.mem_iff_getElem /== ind' indL <- x
    move: (lD (ind' + 1))=> /== /(_ indL) /Set.eq_empty_iff_forall_not_mem lD
    srw ?if_neg // => /μsub // }
  simp=> ind indL ? lD x /== [] In
  { srw ?if_pos // }
  shave ?: x ∉ sht.s
  { move: In=> /shts_set_eqSum /== sht' /List.mem_iff_getElem /== ind' indL <-
    move=> /List.getElem_set; scase_if=> ?
    { move=> /μsub ?; move: (lD 0)=> /== /Set.eq_empty_iff_forall_not_mem // }
    move: (dj (shts[ind']))=> /Set.disjoint_left H /H; sapply
    exact List.getElem_mem shts ind' indL }
  srw ?if_neg //;
  apply ihShts=> // ind'; move: (lD (ind' + 1))=> /==


omit htEq μ_img shts_disj in
private lemma set_set_diff :
  LGTM.SHTs.set (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩) =
    shts.set \ ⟪l, t⟫ ∪ ⟪l, μ '' t⟫ := by
  elim: shts ind=> // sht shts ihShts []
  { simp=> -> /== lD; srw Disjoint.sdiff_eq_left
    { srw Set.union_comm // }
    srw Set.disjoint_left=> a /shts_set_eqSum /== ? /List.mem_iff_getElem /== ind' indL <-
    move: (lD (ind' + 1))=> /== /(_ indL) /Set.eq_empty_iff_forall_not_mem /(_ a) // }
  move=> ind /== indL ? lD; srw ihShts //'
  { srw -Set.union_assoc; congr; srw Set.union_diff_distrib; congr
    refine Eq.symm (Disjoint.sdiff_eq_right ?_)
    refine Set.disjoint_iff_inter_eq_empty.mpr ?_
    sby apply (lD 0) }
  move=> ind'; move: (lD (ind' + 1))=> //

set_option maxHeartbeats 800000 in
lemma triple_merge (Q' : hval αˡ -> hhProp αˡ)
  [uH : FindUniversal H Hu H']
  [uQ : ∀ hv, FindUniversal (Q hv) Qu (Q' hv)]
  [ex : HPropExact uH.univ] :
  shts.set.Nonempty ->
  Hu ==> Qu ->
  hhlocal (shts.set \ ⟪l,t⟫) H' ->
  (∀ hv, hhlocal (shts.set \ ⟪l,t⟫) (Q' hv)) ->
  LGTM.triple (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩) H (fun hv => Q' (hv ∘ μ.liftLab l t) ∗ Hu) ->
  LGTM.triple shts H Q := by
  move=> ? imp Hl Ql htr
  srw uH.H_eq
  shave->: Q = Q' ∗ Qu
  { move=> !hv; rw [(uQ hv).H_eq]; ysimp; ysimp }
  apply LGTM.triple_conseq
  { apply hhimpl_refl }
  { move=> hv /=; apply hhimpl_frame_r; apply imp }
  srw uH.Hu_eq hhstar_comm
  erw [LGTM.triple_extend_univ]=> //' ;rotate_left
  { apply hhlocal_subset; rotate_left=> //'
    apply Set.diff_subset }
  { move=> ?; apply hhlocal_subset; rotate_left=> //'
    apply Set.diff_subset }
  srw LGTM.triple LGTM.wp hwp_ht_eq; rotate_right
  { apply shts_htrm_μ (μ := μ)=> // }
  apply htriple_merge
  { srw -(Set.diff_union_of_subset (s := shts.set) (t := ⟪l, t⟫))
    { srw -bighstar_hhstar_disj -?hhstar_assoc
      { move=> > ![h₁ h₂] H₁ H₂ -> dj
        apply validSubst_union_fun
        { move=> ? /== ?????; srw ?if_neg // }
        { move=> [? x] /== -> ? [? y] /== -> ?; srw ?if_pos //' /==
          move: (H₂ ⟨l, x⟩) (H₂ ⟨l, y⟩); srw /== ?if_pos //'
          move=> /ex.isExact H /H // }
        { shave: hhlocal (shts.set \ ⟪l, t⟫) (H' ∗ [∗ in shts.set \ ⟪l, t⟫| uH.univ])
          { simp [hhlocalE]=> //' }
          sapply=> //' }
        { shave: hhlocal ⟪l, t⟫ ([∗i in ⟪l, t⟫| uH.univ])
          { simp [hhlocalE]=> //' }
          sapply=> //' }
        { exact Set.disjoint_sdiff_left }
        move=> ? ain [? b] *; simp [Function.liftLab]; srw if_neg ?if_pos //
        move: ain => /== ? /[apply] /[swap] -> /==; apply μ_img=> //'; exists b=> // }
      exact Set.disjoint_sdiff_left }
    srw shts_set_eqSum=> ?? /==; exists shts[ind]=> ⟨|⟩
    { srw List.mem_iff_getElem=> //' }
    sby srw shts_ind }
  { simp [hhlocalE]=> //' ?; apply hhlocal_subset; rotate_left=> //'
    apply Set.diff_subset }
  { simp [hhlocalE]=> //' ?; apply hhlocal_subset; rotate_left=> //'
    apply Set.diff_subset }
  srw -[4 6](shtsE (l := l) (t := t)) // -bighstar_hhstar_disj; rotate_left
  { exact Set.disjoint_sdiff_left }
  simp [<-hhstar_assoc]; apply htriple_conseq; rotate_left
  { srw hsubstE
    { srw hhstar_assoc bighstar_hhstar_disj; apply hhimpl_refl; apply disjμ=> //' }
    all_goals sdone }
  { move=> ? /=; srw hsubstE
    { srw hhstar_assoc bighstar_hhstar_disj //; apply disjμ=> //' }
    all_goals sdone }
  srw -(set_set (shts_ind := shts_ind)) //' -(set_set_diff (μ := μ) (shts_ind := shts_ind)) //'
  erw [<-htriple_extend_univ]
  { srw -uH.Hu_eq hhstar_comm -uH.H_eq -hwp_equiv hwp_ht_eq //'
    apply set_htrm=> //' }
  { srw set_set_diff //' /== Set.diff_nonempty
    scase: [⟪l, t⟫.Nonempty]
    { move=> /Set.not_nonempty_iff_eq_empty ->
      left; apply Set.Nonempty.not_subset_empty=> //' }
    srw ?Set.Nonempty.eq_1=> /== x ??; right; exists (μ.liftLab l t x)
    simp; srw if_pos //; }
  { srw set_set_diff; apply hhlocal_subset; rotate_left=> // }
  move=> ? /=; srw set_set_diff; apply hhlocal_subset; rotate_left=> //

end

def LabDisjoint (s₁ s₂ : Set αˡ) : Prop := ∀ l ∈ s₁, ∀ l' ∈ s₂, l.lab ≠ l'.lab
lemma labDisj_disj : LabDisjoint s s' -> Disjoint s s' := by
  srw Set.disjoint_left; move=> dj a /dj H /H //;

@[disjE] lemma LabDisjoint_LabSet : LabDisjoint ⟪l₁, s⟫ ⟪l₂, t⟫ = (l₁ ≠ l₂ ∨ s = ∅ ∨ t = ∅) := by
  simp [LabDisjoint]=> ⟨|⟩
  { scase: [s = ∅]=> //
    scase: [t = ∅]=> //
    srw -?Set.not_nonempty_iff_eq_empty ?Set.Nonempty.eq_1 /== => t tin s sin F
    move: (F ⟨l₁, s⟩ rfl sin ⟨l₂, t⟩ rfl tin)=> // }
  scase=> F [] /= > -> ? [] > /= -> //
  sby scase: F

private lemma fooo : Q = Q' -> Q ==> Q' := by
  move=> ->; apply hhimpl_refl

lemma ymerge_lemma (μ) (shts : LGTM.SHTs αˡ) (Q' : hval αˡ -> hhProp αˡ) ind {_ : ind < shts.length}
  [uH : FindUniversal H Hu H']
  [uQ : ∀ hv, FindUniversal (Q hv) Qu (Q' hv)]
  [ex : HPropExact uH.univ] :
  shts[ind] = ⟨⟪l, t⟫, ht⟩ ->
  t.Nonempty ->
  (∀ x ∈ t, ht ⟨l,x⟩ = ht ⟨l,(μ x)⟩) ->
  μ '' t ⊆ t ->
  shts.Pairwise (LabDisjoint ·.s ·.s) ->
  shts.set.Nonempty ->
  Hu ==> Qu ->
  hhlocal (shts.set \ ⟪l,t⟫) H' ->
  (∀ hv, hhlocal (shts.set \ ⟪l,t⟫) (Q' hv)) ->
  LGTM.triple (List.set shts ind ⟨⟪l, μ '' t⟫, ht⟩) H (fun hv => Q' (fun x => if x.lab = l then hv ⟨l, μ x.val⟩ else hv x) ∗ Hu) ->
  LGTM.triple shts H Q := by
  move=> indE tn ? μ_img dj ???? htr;
  shave lD : ∀ (ind' : ℕ) (h : ind' < List.length shts), ind ≠ ind' → ⟪l, t⟫ ∩ shts[ind'].s = ∅
  { move: dj; srw ?List.pairwise_iff_getElem=> H ind'
    scase: [ind' < ind]=> indL
    { move=> /(H ind) {}H ?
      refine Disjoint.inter_eq ?_; apply labDisj_disj
      srw indE at H; apply H=>//' }
    move=> /(H ind' ind) H *; srw Set.inter_comm
    refine Disjoint.inter_eq ?_; apply labDisj_disj
    srw indE at H; apply H=>//' }
  apply triple_merge (μ := μ)=> //'
  { move: dj; srw ?List.pairwise_iff_get=> H ?? /H /labDisj_disj // }
  srw LGTM.triple LGTM.wp; apply hhimpl_trans; apply htr
  apply hwp_conseq'=> hv /=
  ysimp [fun x ↦ if x.lab = l then hv { lab := l, val := μ x.val } else hv x]
  apply fooo; congr! 1; funext ⟨m,x⟩=> /=; scase_if=> ?/==
  { scase: [x ∈ t]=> /== xin
    { srw set_set_diff /== //' if_neg //== => ⟨|⟩
      { move=> /shts_set_eqSum /== sht /List.mem_iff_getElem /== ind' indL <-
        scase: [ind = ind']=> eq
        { move: dj; srw ?List.pairwise_iff_getElem=> H
          scase: [ind' < ind]=> indL'
          { specialize H ind ind' ?_ ?_ ?_=> //'
            srw indE at H=> /H /== {}H
            scase: tn=> t ?; move: (H ⟨l, t⟩)=> // }
          specialize H ind' ind ?_ ?_ ?_=> //'
          srw indE at H=> /H /== {}H
          scase: tn=> t ?; move: (H ⟨l, t⟩)=> // }
        srw -eq indE // }
      move=> y yin; move: xin=> /[swap] <- /==;
      apply μ_img=> // }
    srw if_pos set_set_diff /== //'; right=> // }
  srw [2]if_neg //
