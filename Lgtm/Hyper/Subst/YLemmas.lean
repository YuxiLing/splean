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


import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.WP
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Subst.Util
import Lgtm.Hyper.ArraysFun

open Classical

notation:max α "ˡ" => Labeled α

def Set.deLab (s : Set αˡ) : Set α := Labeled.val '' s

@[simp]
lemma labSet_deLab :
  ⟪l, s⟫.deLab = s := by
  move=> !?; srw Set.deLab /== => ⟨|?⟨|⟩⟩ /== //

def Function.labLift (f : α -> β) : αˡ -> βˡ := fun x => ⟨x.lab, f x.val⟩

instance [h:Nonempty α] : Nonempty αˡ := by scase: h=> //

section

variable {α : Type} {β : Type}
variable (σ : α -> β)

section

variable (s : Set α) (inj : Set.InjOn σ s)

def hhProp.subst (H : hhProp α) : hhProp β := fun h =>
    ∃ h',
      h = fsubst σ s h' ∧
      H h' ∧
      hlocal s h'

-- omit inj in
@[substE]
lemma subst_hpure :
  ⌜P⌝.subst σ s = ⌜P⌝ := by
  move=> !h !⟨|⟩![]
  { move=> ? -> ![] ? -> ? ⟨|⟩// }
  move=> ? ->; exists ∅=> ⟨|⟨|⟩⟩ //


@[substE]
lemma subst_hhexists (Q : γ -> hhProp α) :
  (∃ʰ x, Q x).subst σ s = ∃ʰ x, (Q x).subst σ s := by
  move=> !h !⟨|⟩ ![]
  { move=> h -> ![x] /= ? ?⟨//|/=⟩⟨|⟩// }
  move=> x h -> ?? ⟨//|⟨|⟨|⟩⟩⟩ //

@[substE]
lemma subst_emp :
  (emp).subst σ s = emp := by
  move=> !h !⟨|⟩![]
  { move=> h -> -> // }
  move=>->; exists ∅=> ⟨|⟨|⟩⟩ //

include inj

lemma fsubst_σ' [Inhabited γ] (f : α -> γ) :
  x ∈ s ->
  fsubst σ s f (σ x) = f x := by
  move=> xin; srw fsubst partialInvSet
  srw dif_pos
  { move=> /=; move: (?hc)=> /choose_spec => []??
    sby apply congrArg; apply inj=> // }
  sdone

lemma subst_bighstar [Nonempty α] :
  s' ⊆ s ->
  (bighstar s' Hs).subst σ s =
  bighstar (σ '' s') (Hs ∘ (σ.invFunOn s)) := by
  move=> ? !h !⟨![h -> si ? a /==]| a⟩
  { scase_if=> [/== a ? <-|/==?]
    { srw Function.invFunOn_app_eq // fsubst_σ' //
      move: (si a)=> /==; srw if_pos // }
    scase: [a ∈ σ '' s]=> [?|/== a ??]
    { srw fsubst_out // fsubst_inE // }
    subst_vars; srw fsubst_σ' //; move: (si a)
    srw if_neg=> // }
  exists fun a => if a ∈ s' then h (σ a) else ∅=> ⟨|⟨|⟩⟩
  { move=> !b; move: (a b); scase_if=> /==
    { move=> a ? <-; srw Function.invFunOn_app_eq // fsubst_σ' // }
    move=> ? /[dup] hE ->
    scase: [b ∈ σ '' s]=> [?|/== b ??]
    { srw fsubst_out // fsubst_inE // }
    subst_vars; srw fsubst_σ' // }
  { move=> x /=; scase_if=> // ?; move: (a (σ x))
    srw if_pos //== Function.invFunOn_app_eq // }
  move=> ??; srw /= if_neg //

lemma subst_hhsingle [Nonempty α] :
  s' ⊆ s ->
  (hhsingle s' p x).subst σ s = hhsingle (σ '' s') (p ∘ (σ.invFunOn s)) (x ∘ (σ.invFunOn s)) := by
  move=> ?; srw subst_bighstar //

@[substE]
lemma subst_hhsingle_const [Nonempty α] :
  s' ⊆ s ->
  (hhsingle s' (fun _ => p) (fun _ => x)).subst σ s = hhsingle (σ '' s') (fun _ => p) (fun _ => x) := by
  move=> ?; srw subst_hhsingle //

omit inj in
@[substE]
lemma subst_if (b : Prop) {dc : Decidable b} (H₁ H₂ : hhProp α) :
  (if b then H₁ else H₂).subst σ s = if b then H₁.subst σ s else H₂.subst σ s := by
  sby scase_if

lemma ssubst_image :
  s' ⊆ s ->
  ssubst σ s s' = σ '' s' := by
  move=> ? !b /==; srw fsubst_inE //
  { srw Set.inter_eq_self_of_subset_right // }
  move=> ???? /inj //

lemma hsubst_hhlocalE :
  hhlocal s H ->
  hsubst σ s H = H.subst σ s := by
  move=> hl !h !⟨|⟩ ![] h -> ?? ⟨|⟨|⟨|⟩⟩⟩ // ???? /inj -> //

set_option maxHeartbeats 800000 in
lemma fsubst_union' (h₁ h₂ : hheap α) :
  fsubst σ s (h₁ ∪ h₂) =
  fsubst σ s h₁ ∪ fsubst σ s h₂ := by
  move=> !b /==
  scase: [∃ a ∈ s, σ a = b]=> /==
  { move=> /== ?; srw ?fsubst partialInvSet
    scase: [∃ a ∈ s, σ a = b]=> /==
    { move=> ?; srw ?dif_neg // }
    move=> y [??]; srw ?dif_pos // }
  move=> a ? <-; srw ?fsubst_σ' //


@[substE]
lemma subst_hhstar (H₁ H₂ : hhProp α) :
  (H₁ ∗ H₂).subst σ s = (H₁.subst σ s) ∗ H₂.subst σ s := by
  move=> !h !⟨|⟩![]
  { move=> ? -> ![h₁ h₂] ?? -> dj hl
    shave hl₁: hlocal s h₁
    { move=> a /hl /==
      move=> eq; apply Finmap.ext_lookup=> l
      move: eq=> /(congrArg (f := Finmap.lookup l))
      scase: [l ∈ h₁ a]=> ?
      { srw [3]Finmap.lookup_eq_none.mpr // }
      srw Finmap.lookup_union_left // }
    shave hl₂: hlocal s h₂
    { move=> a /hl /==
      srw Finmap.union_comm_of_disjoint //
      move=> eq; apply Finmap.ext_lookup=> l
      move: eq=> /(congrArg (f := Finmap.lookup l))
      scase: [l ∈ h₂ a]=> ?
      { srw [3]Finmap.lookup_eq_none.mpr // }
      srw Finmap.lookup_union_left // }
    exists (fsubst σ s h₁), (fsubst σ s h₂)=> ⟨|⟨|⟨|⟩⟩⟩
    { exists h₁ }
    { exists h₂ }
    { srw fsubst_union' // }
    move=> b
    scase: [b ∈ σ '' s]
    { simp=> ?; srw ?fsubst_out // ?fsubst_inE // }
    simp=> ? ? <-; srw ?fsubst_σ' // }
  move=> ?? ![h₁ -> ? hl₁] ![h₂ -> ? hl₂] -> dj
  exists (h₁ ∪ h₂)=> ⟨|⟨|⟩⟩ /==
  { srw fsubst_union' // }
  { exists h₁, h₂=> ⟨|⟨|⟨|⟩⟩⟩ // a
    scase: [a ∈ s]=> ?
    { srw hl₁ ?hl₂ // }
    move: (dj (σ a)); srw ?fsubst_σ' // }
  move=> ?? /=; srw hl₁ ?hl₂ //

open EmptyPCM in
@[substE]
lemma subst_hharray_const [Nonempty α] :
  s' ⊆ s ->
  (hharrayFun s' f n (fun _ => p)).subst σ s = hharrayFun (σ '' s') f n (fun _ => p) := by
  move=> ?;
  srw ?hharrayFun_eq_hhadd ?hhaddE subst_hhstar // subst_hhsingle_const; congr
  move: (⟦0,n⟧)=> fs
  induction fs using Finset.induction_on=> // /==
  apply subst_emp
  rename_i a s ain ihfs
  srw ?Finset.sum_insert // ?hhaddE subst_hhstar // subst_hhsingle_const //



end

lemma Set.InjOn_union_left (s₁ s₂ : Set α) :
  (s₁ ∪ s₂).InjOn f -> s₁.InjOn f := by
  move=> inj ???? /inj //

lemma Set.InjOn_union_right (s₁ s₂ : Set α) :
  (s₁ ∪ s₂).InjOn f -> s₂.InjOn f := by
  move=> inj ???? /inj //

lemma shts_set_eqSum (shts : LGTM.SHTs α) :
  shts.set = ⋃ i ∈ shts, i.s := by
  elim: shts=> //

variable [nα : Nonempty α]

@[irreducible]
noncomputable def LGTM.SHTs.subst (shts : LGTM.SHTs αˡ) : LGTM.SHTs βˡ :=
  shts.map fun ⟨s, ht⟩ => ⟨σ.labLift '' s, ht ∘ (σ.labLift.invFunOn s)⟩

@[simp]
lemma shts_subst_cons (shts : LGTM.SHTs αˡ) :
  LGTM.SHTs.subst σ (⟨s, ht⟩ :: shts) = (⟨σ.labLift '' s, ht ∘ (σ.labLift.invFunOn s)⟩ :: shts.subst σ) :=
  by unfold LGTM.SHTs.subst=> /==

@[simp]
lemma shts_subst_emp :
  LGTM.SHTs.subst σ [] = [] := by
  unfold LGTM.SHTs.subst=> /==

lemma htrm_subst_σ (shts : LGTM.SHTs αˡ) :
  shts.set.InjOn σ.labLift  ->
  shts.Pairwise (Disjoint ·.s ·.s) ->
  shts.set.EqOn shts.htrm ((shts.subst σ).htrm ∘ σ.labLift) := by
  elim: shts=> //== [] /== s ht shts ih inj dj₁ dj₂ ⟨|⟩
  { move=> [l a] /== ?
    srw ?if_pos // Function.invFunOn_app_eq //
    sby apply Set.InjOn_union_left }
  move=> [l a] /==; srw shts_set_eqSum /==
  scase=> s' ht' => /= ??
  srw ?if_neg //
  { apply ih=> //; apply Set.InjOn_union_right=> //
    srw shts_set_eqSum=> /== ⟨|//⟩ }
  { simp=> > ? /inj /== ⟨//|⟨|⟩⟩
    { right;srw shts_set_eqSum=> /== ⟨|//⟩  }
    move: x=> > /[swap] ->; eapply Set.disjoint_left.mp
    { srw disjoint_comm; apply dj₁=> // }
    sdone }
  eapply Set.disjoint_left.mp
  { srw disjoint_comm; apply dj₁=> // }
  sdone

lemma set_subst_σ (shts : LGTM.SHTs αˡ) :
  σ.labLift '' shts.set = (shts.subst σ).set := by
  elim: shts=> // /== [s ht] /== shts
  srw Set.image_union //


attribute [simp] LGTM.SHTs.subst

lemma ysubst_lemma_aux (Q : hval αˡ -> hhProp αˡ) (σ : α -> β)
  (shts : LGTM.SHTs αˡ):
  shts.Pairwise (Disjoint ·.s ·.s) ->
  hhlocal shts.set H ->
  (∀ hv, hhlocal shts.set (Q hv)) ->
  Set.InjOn σ.labLift shts.set ->
  (H.subst σ.labLift shts.set ==> LGTM.wp (shts.subst σ) fun hv => Q (hv ∘ σ.labLift) |>.subst σ.labLift shts.set ) ->
  H ==> LGTM.wp shts Q := by
  move=> dj hl₁ hl₂ inj himp
  srw LGTM.wp hwp_ht_eq; rotate_right; apply (htrm_subst_σ (σ := σ))=> //
  apply hwp_hsubst=> //
  srw !hsubst_hhlocalE // hwp_Q_eq; rotate_right
  { move=> ?; srw !hsubst_hhlocalE // }
  srw ssubst_image // set_subst_σ //

class SubstTypeUniversal (Hα : hhProp α) (Hβ : outParam (hhProp β)) :=
  univ : hProp
  Hα_eq : Hα = [∗ in Set.univ | univ]
  Hβ_eq : Hβ = [∗ in Set.univ | univ]

omit [Nonempty α] in
lemma hhlocal_subst (H : hhProp α) :
  hhlocal (σ '' s) (H.subst σ s) := by
  move=>  h ![h] -> _ _ l /== ?
  srw fsubst_out // fsubst_inE //

lemma ysubst_lemma (Q Q' : hval αˡ -> hhProp αˡ) (σ : α -> β)
  [uH : FindUniversal H Hu H']
  [uQ : ∀ hv, FindUniversal (Q hv) Qu (Q' hv)]
  [sub : SubstTypeUniversal Hu Hu']
  (shts : LGTM.SHTs αˡ):
  Hu ==> Qu ->
  shts.set.Nonempty ->
  shts.Pairwise (Disjoint ·.s ·.s) ->
  hhlocal shts.set H' ->
  (∀ hv, hhlocal shts.set (Q' hv)) ->
  Set.InjOn σ.labLift shts.set ->
  (Set.InjOn σ.labLift shts.set ->
    (H'.subst σ.labLift shts.set ∗ Hu' ==>
    LGTM.wp (shts.subst σ) (fun hv => ((Q' (hv ∘ σ.labLift) |>.subst σ.labLift shts.set) ∗ Hu')))) ->
  H ==> LGTM.wp shts Q := by
  move=> imp nemp *
  srw uH.H_eq
  shave->: Q = Q' ∗ Qu
  { move=> !hv; rw [(uQ hv).H_eq]; ysimp; ysimp }
  apply LGTM.triple_conseq
  { apply hhimpl_refl }
  { move=> hv /=; apply hhimpl_frame_r; apply imp }
  srw uH.Hu_eq hhstar_comm
  erw [LGTM.triple_extend_univ]
  apply ysubst_lemma_aux=> //
  srw subst_hhstar //=
  srw LGTM.wp_Q_eq; rotate_right
  { move=> ?; srw subst_hhstar // }
  srw subst_bighstar //= set_subst_σ // Function.comp
  move: (LGTM.triple_extend_univ
    (shts := shts.subst σ)
    (H := hhProp.subst (Function.labLift σ) shts.set H')
    (H' := FindUniversal.univ H)
    (Q := fun hv ↦ hhProp.subst σ.labLift shts.set (Q' (hv ∘ σ.labLift))))
  simp=> H; apply (H ..).mp=> //<;> clear H
  { shave<-: sub.univ = uH.univ
    { move: (uH.Hu_eq); srw (sub.Hα_eq)=> /congrFun heq !h
      move: (heq fun _ => h); srw ?bighstar ?bighstarDef
      scase: nα=> a _ /== [H₁ H₂] ⟨|⟩ ?
      { apply H₁=> // }
      apply H₂=> // }
    srw -sub.Hβ_eq // }
  { scase: nemp=> x ?; exists (σ.labLift x)
    srw -set_subst_σ // }
  { srw -set_subst_σ; apply hhlocal_subst }
  srw -set_subst_σ=> ?; apply hhlocal_subst

class SHTsSubst (shts : LGTM.SHTs αˡ) (σ : α -> β) (shts' : outParam (LGTM.SHTs βˡ)) :=
  eq : shts' = shts.subst σ

instance : SHTsSubst [] σ [] where
  eq := by simp
end
