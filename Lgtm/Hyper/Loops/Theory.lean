import Lean

-- lemmas on heaps
import Mathlib.Data.Finmap

-- lemmas about big operators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

-- lemmas about intervals
import Mathlib.Data.Int.Interval

-- big union over sets
import Mathlib.Data.Set.Semiring
import Mathlib.Data.Finset.Sups

import Lgtm.Common.Util
import Lgtm.Unary.SepLog
import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Arrays

open Classical trm val prim
open SetSemiring

set_option linter.style.longFile 1900

section

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

instance : AddCommMonoid (Set α) := SetSemiring.instAddCommMonoid
instance : Inhabited hhProp := ⟨fun _ => False⟩
attribute [instance 0] PartialCommMonoid.toAddCommSemigroup
attribute [-simp] hhwandE


@[simp]
lemma disjoint_union (sᵢ : β -> Set α)  :
  Disjoint s (∑ i in fs, sᵢ i) =
  (∀ x ∈ fs, Disjoint s (sᵢ x)) := by sorry

@[simp]
lemma disjoint_union' (sᵢ : β -> Set α)  :
  Disjoint (∑ i in fs, sᵢ i) s =
  (∀ x ∈ fs, Disjoint (sᵢ x) s) := by sorry

lemma mem_union (sᵢ : β -> Set α) :
  (x ∈ ∑ i ∈ fs, sᵢ i) = ∃ i ∈ fs, x ∈ sᵢ i := by sorry

lemma sum_set_eq_iunion (sᵢ : β -> Set α) :
  ⋃ i ∈ fs, sᵢ i = ∑ i in fs, sᵢ i := by
  move=> !x /==; simp [mem_union]


@[simp]
lemma set_plusE (s₁ s₂ : Set α) : s₁ + s₂ = s₁ ∪ s₂ := by rfl
@[simp]
lemma sot_0E  : (0 : Set α) = ∅ := by rfl


macro_rules
  | `(tactic| ssr_triv) => `(tactic| omega)

-- namespace LGTM

@[simp]
lemma semiring.down (s : SetSemiring α) : SetSemiring.down s = s := by rfl

namespace Disjoint

section ForLoop

lemma LGTM.wp_for_aux
  (z i n : Int)
  (Inv : Int -> hval -> hhProp)
  (sᵢ : Int -> Set α)
  (ht c : htrm) :
  z <= i ∧ i <= n ->
  (∀ j hv₁ hv₂, i <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  s = ∑ i in ⟦i, n⟧, sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
     Inv j hv ==>
      LGTM.wp
           [⟨s', fun i => subst vr j (c i)⟩, ⟨sᵢ j, ht⟩]
           (fun hv' => Inv (j + 1) (hv ∪_(∑ i in ⟦z, j⟧, sᵢ i) hv'))) ->
  Inv i hv₀ ==>
    LGTM.wp
         [⟨s', fun j => trm_for vr i n (c j)⟩, ⟨s, ht⟩]
         (fun hv => Inv n (hv₀ ∪_(∑ i in ⟦z, i⟧, sᵢ i) hv)) := by
  move=> iin Heq dij seq sij' ind
  shave H: i <= n; omega; move: i H hv₀ s seq iin Heq
  apply Int.le_induction_down
  { move=> > ?-> ? Heq
    srw Finset.Ico_self /== LGTM.wp_cons /=
    ychange hwp_for'=> /==
    srw LGTM.wp /== hwp0_dep; ysimp[hv₀]
    apply Heq=> // }
  move=> i ? ih hv₀ ? sij' seq ? Heq
  srw LGTM.wp_cons /=; ychange hwp_for=> /==
  { omega }
  { sdone }
  srw -(LGTM.wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ (_ ∪__ x)))
  srw sum_Ico_succl
  ychange LGTM.wp_align_step_disj
  { simp at sij'; apply sij'=> /==; omega }
  { move: sij'; srw sum_Ico_succl /= /==; omega }
  { simp=> /== *;
    apply dij=> /== <;> omega }
  { omega }
  { simp=> ⟨|⟩
    { simp at sij'; apply sij'=> /==; omega }
    move: sij'; srw sum_Ico_succl /==; omega }
  { omega }
  ychange ind
  { rw [foo''']; omega }
  apply hwp_conseq=> hv /==
  -- scase: [i = n]=> [?|->]
  ychange (ih (s := ∑ i ∈ ⟦i, n⟧, sᵢ i)) <;> try trivial
  { move: sij'; srw sum_Ico_succl /==; omega }
  { omega }
  { move=> ???? /Heq; sapply; omega }
  apply hwp_conseq=> hv' /=
  srw -fun_insert_assoc [2]sum_Ico_predr=> [//|]
  omega


lemma LGTM.wp_conseq :
  Q ===> Q' ->
  LGTM.wp sht Q ==> LGTM.wp sht Q' := by
  apply hwp_conseq

set_option maxHeartbeats 800000 in
lemma LGTM.wp_for (Inv : Int -> hval -> hhProp) (sᵢ : Int -> Set α) (ht c : htrm) :
   (z <= n) ->
   (∀ j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
   Disjoint s' s ->
   (∀ j hv, z <= j ∧ j < n ->
      Inv j hv ==>
        LGTM.wp [⟨s', fun i => subst vr j (c i)⟩, ⟨sᵢ j, ht⟩] (fun hv' => Inv (j + 1) (hv' ∪_(sᵢ j) hv))) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (s = ∑ i in ⟦z, n⟧, sᵢ i) ->
  (P ==> Inv z hv₀) ->
  (Inv n ===> Q) ->
   P ==> LGTM.wp [⟨s', fun i => trm_for vr z n (c i)⟩, ⟨s, ht⟩] Q := by
     move=> ? inveq disj ind dij seq pimpl implq
     ychange pimpl
     ychange LGTM.wp_conseq; apply implq
     ychange (LGTM.wp_for_aux (sᵢ := sᵢ) (i := z) (z := z) (n := n))=> //
     rotate_right
     { sby apply LGTM.wp_conseq=> ? }
     move=> > ?; ychange ind=> //'
     apply hwp_conseq'=> hv' /==
     ysimp[hv]; apply inveq=> //'
     move=> x /==
     simp at disj
     split_ifs=> //
     case pos h₁ h₂=>
       move: h₂ h₁; srw mem_union=> ![]/== j' *
       shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
       sby apply dij=> /==

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

variable [PartialCommMonoid val]

-- lemma sum_bighstar (H : β -> α -> hProp) :
--   -- Finset.sum fs (bighstar s H)=
--   ∑ i in fs, H i ∗↑ s = [∗ a in s| ∑ i in fs, H i a] := by sorry
open EmptyPCM  in
omit [PartialCommMonoid val] in
lemma sum_bighstar_set (H : α -> hProp) (s : β -> Set α) :
  -- Finset.sum fs (bighstar s H)=
  (∀ᵉ (i ∈ fs) (j ∈ fs), i != j -> Disjoint (s i) (s j)) ->
  H ∗↑ ∑ i in fs, s i = ∗∗ i in fs, H ∗↑ s i := by
  induction fs using Finset.induction_on=> //==
  srw ?(@Finset.sum_insert) // /== => dj djs
  srw -bighstar_hhstar_disj /== //
  move=> *; apply dj=> // ? //

omit [PartialCommMonoid val] in
lemma hhimpl_bighstar_himpl
   (Q R : α -> hProp) (s : Set α) :
  (∀ x ∈ s, himpl (Q x) (R x)) ->
  [∗ i in s| Q i] ==> [∗ i in s| R i] := by
  move=> imp a; srw ?bighstar ?bighstarDef /=
  move=> H a; move: (H a); scase_if=> //

omit [PartialCommMonoid val] in
lemma choose_fun2 {α β γ : Type}  [Inhabited β] [Inhabited γ]
   (p : α -> β -> γ -> Prop) (s : Set α) :
  (∀ a ∈ s, ∃ b c, p a b c) -> (∃ (f : α -> β) (g : α -> γ), (∀ a ∈ s, p a (f a) (g a))) := by
  move=> pH
  shave: (∀ a ∈ s, ∃ (bc : β×γ), p a bc.fst bc.snd)
  { move=> ? /pH ![b c] ?; exists (b,c)=> //  }
  move=> /choose_fun /(_ ((default : β), (default : γ)))[f] ?
  exists (f · |>.fst), (f · |>.snd)

-- #check instAddHhPropOfPartialCommMonoidVal

omit [PartialCommMonoid val] in
lemma congr_hhimpl :
  H = H' ->
  H ==> H' := by move=>-> //

open EmptyPCM in
set_option maxHeartbeats 1600000 in
lemma LGTM.wp_for_bighop (β : Type) [inst : Inhabited β]
  {c : htrm}
  (z n : Int)
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  s = ∑ i in ⟦z, n⟧, sᵢ i ->
  (∀ (hv : hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i hv = Qgen j v ∗ H) ->
  Disjoint s' s ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (∀ j v, z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun i => subst vr j (c i)⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗ R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun i => trm_for vr z n (c i)⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> ? eqQ ? gen dj dij' ind *
  eapply wp_for
    (hv₀ := fun _ => default)
    (Inv := fun i hv =>
      H₀ +
      (∑ j in ⟦z, i⟧, Q j hv) ∗
       Inv i ∗
      ((∗∗ j in ⟦z, i⟧, R' ∗↑ sᵢ j) ∗ (∗∗ j in ⟦i, n⟧, R ∗↑ sᵢ j)))=> //'
  { move=> > ? hveq; ysimp;-- srw ?sum_bighstar; apply hhimpl_bighstar_himpl=> a ?
    srw (Finset.sum_congr (s₂ := ⟦z,j⟧)); rotate_right 2
    { move=> /== k ??; apply eqQ
      { auto }
      move=> ??; apply hveq=> xin
      sapply: (Set.disjoint_left.mp dj xin)
      srw mem_union; exists k=> ⟨|//⟩ /==; omega }
    all_goals auto }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' /==
    ychange ind=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp
    apply hhimpl_trans; apply hhadd_hhsatr_assoc
    srw sum_Ico_predr //' -gen //' /== add_left_comm [2]add_comm
    apply congr_hhimpl; congr 2
    { apply Finset.sum_congr=> //'
      move=> /== k ??; apply eqQ=> //' ? f /==
      specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
      move: (Set.disjoint_left.mp dij' f)=> //' }
    apply eqQ=> //' }
  { srw Finset.Ico_self /== //'; subst_vars; srw -sum_bighstar_set
    { erw [add_zero]; ysimp }
    move=> /== *; apply dij' => //' }
  move=> hv' /=; subst_vars; srw sum_bighstar_set ?Finset.Ico_self /==;
  ysimp
  move=> /== *; apply dij' => //'


end ForLoop

section WhileLoop

set_option maxHeartbeats 1600000 in
lemma LGTM.wp_while_aux_false (Inv : Int -> hval -> hhProp)  (sᵢ : Int -> Set α) :
  (∀ j hv, z <= j ∧ j < n ->
    Inv j hv ==>
      LGTM.wp
        [⟨sᵢ j, ht⟩]
          (fun hv' => Inv (j+1) (hv ∪_(∑ i in ⟦z, j⟧, sᵢ i) hv'))) ->
  (z <= i ∧ i <= n) ->
  (∀ j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (s = ∑ i in ⟦i, n⟧, sᵢ i) ->
  Disjoint s' s ->
  Inv i hv₀ ==>
    LGTM.wp
         [⟨s, ht⟩]
         (fun hv => Inv n (hv₀ ∪_(∑ i in ⟦z, i⟧, sᵢ i) hv) ) := by
    move=> ind []L₁ L₂ Inveq disj; move: i L₂ L₁ s hv₀
    apply Int.le_induction_down
    { move=> ?? hv₀ ->/==; srw LGTM.wp /== hwp0_dep; ysimp[hv₀]
      apply Inveq=> //' }
    move=> j ? ih ? s hv₀ ->
    srw sum_Ico_succl /==; intros _ dij=> //'
    srw -(fun_insert_ff (s := sᵢ (j - 1)) (f := ht))
    srw -LGTM.wp_unfold_first
    ychange ind
    { sby srw foo''' }
    { simp=> *; apply disj=> /== <;> omega }
    simp; srw ?LGTM.wp_cons /=; apply hwp_conseq
    { move=> hv /=; srw LGTM.wp /== hwp0_dep; ysimp=> ?
      ychange ih <;> try trivial
      { omega }
      { simp=> // }
      apply hwp_conseq=> ?; apply Inveq
      { sdone }
      srw [2]sum_Ico_predr /==; intros
      split_ifs=> // }
    { simp=> *; apply disj=> /== <;> omega }
    sdone


set_option maxHeartbeats 1600000 in
lemma LGTM.wp_while_aux
  (z i n : Int)
  (Inv : Bool -> Int -> hval -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= i ∧ i <= n ->
  (∀ b j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv b j hv₁ ==> Inv b j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  s = ∑ i in ⟦i, n⟧, sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv true j hv ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' => ∃ʰ b, Inv b (j + 1) (hv ∪_(∑ i in ⟦z, j⟧, sᵢ i) hv'))) ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv false j hv ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Inv false (j + 1) (hv ∪_(∑ i in ⟦z, j⟧, sᵢ i) hv'))) ->
  (∀ j b hv, z <= j ∧ j <= n ->
    Inv b j hv ==> hwp s' (fun _ => cnd) (fun bv => ⌜bv = fun _ => val.val_bool b⌝ ∗ Inv b j hv)) ->
  (∀ hv b, Inv b n hv ==> ⌜b = false⌝ ∗ Inv b n hv) ->
  Inv b₀ i hv₀ ==>
    LGTM.wp
         [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩]
         (fun hv => Inv false n (hv₀ ∪_(∑ i in ⟦z, i⟧, sᵢ i) hv)) := by
    move=> []L₁ L₂ Inveq disj seq dij indt indf cndE cndn
    scase: b₀
    { clear indt
      srw LGTM.wp_cons /=; ychange hwp_while=> //'
      ychange cndE=> //'; apply hwp_conseq=> hv /=
      ysimp; ychange hwp_if
      apply htriple_val
      apply hhimpl_trans; apply LGTM.wp_while_aux_false=> //
      apply hwp_conseq=> ? /=; apply Inveq=> //' }
    move: i L₂ L₁ s hv₀  seq
    apply Int.le_induction_down
    { move=> ???? ->/==; ychange cndn=> //' }
    move=> j ? ind ? s dij hv₀ ?
    srw LGTM.wp_cons /=; ychange hwp_while=> //'
    ychange cndE
    { sby srw foo''' }
    apply hwp_conseq=> hv /=
    ysimp; ychange hwp_if
    srw -(LGTM.wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ _ (_ ∪__ x)))
    srw sum_Ico_succl
    ychange LGTM.wp_align_step_disj
    { simp at dij; apply dij=> /==; omega }
    { move: dij; srw sum_Ico_succl /==; omega }
    { simp=> /== *; apply disj=> /== <;> omega }
    { omega }
    { simp=> ⟨|⟩
      { simp at dij; apply dij=> /==; omega }
      move: dij; srw sum_Ico_succl /==; omega }
    { omega }
    ychange indt
    { sby srw foo'''; omega }
    apply hwp_conseq=> hv /==
    shave ?: Disjoint s' (∑ i ∈ ⟦j, n⟧, sᵢ i)
    { move: dij; srw sum_Ico_succl /==; omega }
    ysimp=> []
    { srw LGTM.wp_cons /=;
      apply hhimpl_trans_r; apply hwp_while=> //'
      apply hhimpl_trans; apply cndE
      { omega }
      apply hwp_conseq=> hv /=
      apply hhimpl_hstar_hhpure_l=> -> /=
      apply hhimpl_trans_r; apply hwp_if=> /=
      apply htriple_val
      apply hhimpl_trans; apply LGTM.wp_while_aux_false <;> try trivial
      { omega }
      { sdone }
      apply hwp_conseq=> ? /=; apply Inveq=> //' /==
      srw sum_Ico_predr /==; intros
      split_ifs=> // }
    apply hhimpl_trans; apply (ind (s := ∑ i in ⟦j, n⟧, sᵢ i)) <;> try trivial
    { omega }
    apply hwp_conseq=> hv' /=
    srw -fun_insert_assoc [2]sum_Ico_predr=> [//|]
    omega

set_option maxHeartbeats 1600000 in
lemma LGTM.wp_while
  (z n : Int)
  (Inv : Bool -> Int -> hval -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= n ->
  (∀ b j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv b j hv₁ ==> Inv b j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  s = ∑ i in ⟦z, n⟧, sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv true j hv ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' => ∃ʰ b, Inv b (j + 1) (hv' ∪_(sᵢ j) hv))) ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv false j hv ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Inv false (j + 1) (hv' ∪_(sᵢ j) hv))) ->
  (∀ j b hv, z <= j ∧ j <= n ->
    Inv b j hv ==> hwp s' (fun _ => cnd) (fun bv => ⌜bv = fun _ => val.val_bool b⌝ ∗ Inv b j hv)) ->
  (∀ hv b, Inv b n hv ==> ⌜b = false⌝ ∗ Inv b n hv) ->
  (P ==> Inv b₀ z hv₀) ->
  (Inv false n ===> Q) ->
  P ==> LGTM.wp [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩] Q := by stop
    move=> ? inveq disj seq dij indt indf cndE cndn pimpl implq
    ychange pimpl
    ychange LGTM.wp_conseq; apply implq
    ychange (LGTM.wp_while_aux (sᵢ := sᵢ) (n := n) (z := z)) <;> try trivial
    rotate_right
    { sby apply LGTM.wp_conseq=> ? }
    { move=> > ?; ychange indt=> //'
      apply hwp_conseq'=> hv' /==
      ypull=> b
      ysimp[hv, b]; apply inveq=> //'
      move=> x /==
      simp at dij
      split_ifs=> //
      case pos h₁ h₂=>
        move: h₂ h₁; srw mem_union=> ![]/== j' *
        shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
        sby apply disj=> /== }
    move=> > ?; ychange indf=> //'
    apply hwp_conseq'=> hv' /==
    ysimp[hv]; apply inveq=> //'
    move=> x /==
    simp at dij
    split_ifs=> //
    case pos h₁ h₂=>
      move: h₂ h₁; srw mem_union=> ![]/== j' *
      shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
      sby apply disj=> /==

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q
set_option maxHeartbeats 1600000 in
open EmptyPCM in
lemma LGTM.wp_while_bighop [PartialCommMonoid val] (β : Type) [inst : Inhabited β]
  (z n : Int)
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Bool -> Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  -- s'.Nonempty ->
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  s = ∑ i in ⟦z, n⟧, sᵢ i ->
  (∀ (hv : hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i hv = Qgen j v ∗ H) ->
  Disjoint s' s ->
  (∀ (i j : ℤ), (i != j) = true → z ≤ i ∧ i < n → z ≤ j ∧ j < n → Disjoint (sᵢ i) (sᵢ j)) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv true j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          fun hv' =>
          Q j hv' + Qgen j v ∗ (∃ʰ b, (Inv b (j + 1))) ∗ R' ∗↑ (sᵢ j)) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Q j hv' + Qgen j v ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => ⌜(bv = fun _ => val.val_bool b)⌝ ∗ Inv b j)) ->
  (∀ b, Inv b n ==> ⌜b = false⌝ ∗ Inv b n) ->
  H₀ ∗ Inv b₀ z ∗ R ∗↑ s ==>
    LGTM.wp [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩]
      fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv false n ∗ R' ∗↑ s := by
  move=> ? eqQ ? gen dj dij' indt indf cndE cndn
  eapply LGTM.wp_while
    (z := z)
    (n := n)
    (hv₀ := fun _ => default)
    (Inv := fun b i hv =>
      H₀ +
      (∑ j in ⟦z, i⟧, Q j hv) ∗
       Inv b i ∗
      ((∗∗ j in ⟦z, i⟧, R' ∗↑ sᵢ j) ∗ (∗∗ j in ⟦i, n⟧, R ∗↑ sᵢ j)))=> //'
  { move=> > ? hveq; ysimp
    srw (Finset.sum_congr (s₂ := ⟦z,j⟧)); rotate_right 2
    { move=> /== k ??; apply eqQ
      { auto }
      move=> ??; apply hveq=> xin
      sapply: (Set.disjoint_left.mp dj xin)
      srw mem_union; exists k=> ⟨|//⟩ /==; omega }
    all_goals auto }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' /==
    ychange indt=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp=> ?
    apply hhimpl_trans; apply hhadd_hhsatr_assoc
    srw sum_Ico_predr //' -gen //' /== add_left_comm [2]add_comm
    apply congr_hhimpl; congr 2
    { apply Finset.sum_congr=> //'
      move=> /== k ??; apply eqQ=> //' ? f /==
      specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
      move: (Set.disjoint_left.mp dij' f)=> //' }
    apply eqQ=> //  }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' /==
    ychange indf=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp=> ?
    apply hhimpl_trans; apply hhadd_hhsatr_assoc
    srw sum_Ico_predr //' -gen //' /== add_left_comm [2]add_comm
    apply congr_hhimpl; congr 2
    { apply Finset.sum_congr=> //'
      move=> /== k ??; apply eqQ=> //' ? f /==
      specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
      move: (Set.disjoint_left.mp dij' f)=> //' }
    apply eqQ=> //  }
  { move=> > ?; specialize cndE j b
    srw -hwp_equiv at cndE; ychange cndE=> //'
    apply hhimpl_trans; apply hwp_frame;
    apply hwp_conseq=> ?; ysimp }
  { move=> ??; ychange cndn; ysimp }
  { srw Finset.Ico_self /== -sum_bighstar_set;
    { erw [add_zero]; ysimp; ysimp }
    move=> /== *; apply dij' => //'}
  move=> ? /=; srw Finset.Ico_self -sum_bighstar_set /==;
  { ysimp; ysimp }
  move=> /== *; apply dij' => //'

end WhileLoop

end Disjoint

lemma LGTM.wp_sht_eq (shts shts' : LGTM.SHTs α) :
  (shts.Forall₂ (fun sht sht'=> sht.s = sht'.s ∧ ∀ x ∈ sht.s, sht.ht x = sht'.ht x) shts') ->
  LGTM.wp shts Q = LGTM.wp shts' Q := by
  move=> ?
  srw ?LGTM.wp
  shave<-: shts.set = shts'.set
  { elim: shts shts'=> // sht shts ihst [] // sht' shts' /== -> _ /ihst -> }
  apply hwp_ht_eq
  elim: shts shts'=> // sht shts ihst [] // sht' shts' /== -> eq /ihst eq ⟨|⟩
  { move=> ??; srw ?fun_insert ?if_pos // }
  move=> ??; srw ?fun_insert; scase_if=> //

namespace ForLoopAux

def labSet (l : ℤ) (s : Set α) : Set (ℤ × α) := {(l, a) | a ∈ s}

local notation (priority := high) "⟪" l ", " s "⟫" => labSet l s

@[simp]
lemma labelSet_inE :
  ((l, a) ∈ ⟪l', s⟫) = (l = l' ∧ a ∈ s) := by
  simp [labSet]=> //

@[simp]
lemma labelSet_inE' :
  (⟪l', s⟫ (l, a)) = (l = l' ∧ a ∈ s) := by
  apply labelSet_inE


private lemma foo (s : Set α) :
  s a = (a ∈ s) := by rfl

variable (z n : ℤ)
variable (sᵢ : ℤ -> Set α)
variable (s' : Set α)
variable (disj : Disjoint s' s)
variable (seq: s = ∑ i in ⟦z, n⟧, sᵢ i)
variable (df : α)
variable (dfN : df ∉ s' ∪ s)

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

private noncomputable def π' : ℤ × α -> α :=
  fun (i, a) =>
    if i ∈ ⟦z,n⟧ then
      if a ∈ sᵢ i then a
      else df
    else
      if i = n then
        if a ∈ s' then a
        else df
      else df

private noncomputable def κ' : α -> ℤ × α :=
  fun a => if a ∈ s' then (n, a) else (n+1, df)


local notation "π" => π' z n sᵢ s' df
local notation "κ" => κ' n s' df

attribute [simp] π' κ' mem_union

@[simp]
abbrev fs := ∑ i in ⟦z,n⟧, ⟪i, sᵢ i⟫

local notation "fs" => fs z n sᵢ

section

include seq disj dfN

omit dfN in
private lemma disj' :
  ∀ i a, a ∈ s' -> a ∈ sᵢ i -> z <= i ∧ i < n -> False := by
  move=> i *
  srw seq /== at disj
  simp at disj
  specialize disj i ?_ ?_=> //'
  move: (Set.disjoint_left.mp disj)=> //

local notation "disj'" => disj' s z n sᵢ s' disj seq

set_option maxHeartbeats 1600000 in
@[simp]
private lemma validSubst_s' :
  validSubst π (⟪n,s'⟫ ∪ fs) ⟪n, s'⟫ := by
  move: (disj')=> d
  simp=> []/== > [/== -> ? | > /== > ?? -> ? > [/== -> ? | /== ? ?? -> ? ] ]
  { move=> > /== [/== -> ?| /== ? ?? -> ? ]
    { srw if_pos //' }
    srw if_pos //' if_pos //' if_pos //' => -> ⟨|⟩ //' *
    exfalso; apply d=> //' }
  { srw if_pos //' if_pos //' if_neg //' if_pos //' if_pos //' => ?
    subst_vars=> ⟨|⟩ //' /== ?; exfalso; apply d=> //' }
  srw if_pos //'

set_option maxHeartbeats 1600000 in
@[simp]
private lemma validSubst_s :
  validSubst π (⟪n,s'⟫ ∪ fs) fs := by
  move: (disj')=> d
  simp=> []/== > [/== -> ? | > /== > ?? -> ? > [/== -> ? | /== y ?? -> ? ] ]
  { move=> > /== [/== -> ?| /== ? ?? -> ? ]
    { srw if_pos //' }
    srw if_pos //' if_pos //' if_pos //' => ? ⟨|⟩ //'; subst_vars
    { srw (@foo (ℤ×α) (n, b) (∑ i ∈ ⟦z, n⟧, ⟪i, sᵢ i⟫)) /== //' }
    srw (@foo (ℤ×α) (_, b) (∑ i ∈ ⟦z, n⟧, ⟪i, sᵢ i⟫)) /== => *
    subst_vars; exfalso; apply d=> //' }
  { srw if_pos //' if_pos //' if_neg //' if_pos //' if_pos //' => ?
    subst_vars=> ⟨|⟩ //' /== f; exfalso; apply d=> //'
    move: f; srw (@foo (ℤ×α) (n, b) (∑ i ∈ ⟦z, n⟧, ⟪i, sᵢ i⟫)) /== //' }
  srw if_pos //' if_pos //' if_pos //' if_pos //'=> ?; subst_vars
  srw ?(@foo (ℤ×α) _ (∑ i ∈ ⟦z, n⟧, ⟪i, sᵢ i⟫)) /== => ⟨|⟩ /== *
  exists y; exists x

private lemma ssubst_s' :
  ssubst π (⟪n, s'⟫ ∪ fs) ⟪n, s'⟫ = s' := by
  move=>!x; srw fsubst_inE; rotate_right
  { apply validSubst_s'=> // }
  simp=> ⟨|⟩ /==
  { move=> > [] // }
  move=> ?; exists n, x=> //

private lemma ssubst_s :
  ssubst π (⟪n, s'⟫ ∪ fs) fs = s := by
  move=>!x; srw fsubst_inE; rotate_right
  { apply validSubst_s=> // }
  simp=> ⟨|⟩ /==
  { move=> > [] //== > ?????????
    srw if_pos //' if_pos //'=> ?; subst_vars=> /== ⟨|//⟩ }
  srw seq=> /== i ???; exists i, x=> // ⟨⟨|⟩|⟩
  { right; exists i }
  { exists i }
  srw if_pos=> //

omit disj in
private lemma lem0 : (df ∉ s') ∧ (∀ i, z <= i -> i < n -> df ∉ sᵢ i) := by
  move: seq dfN=> -> /==


set_option maxHeartbeats 1600000 in
private lemma lem1 :
  (∀ a ∈ fs, ∀ a' ∉ fs, π a ≠ π a') := by
  move: (lem0 s z n sᵢ s' seq df dfN)=> [? ?]
  move: (disj') => d
  move=> [] > /== ? ?? -> ? > ?
  srw if_pos //' if_pos //'; scase_if=> /==
  { move=> ??; srw if_neg //' => ? // }
  move=> ?; scase_if=> [?|]
  { scase_if=> ?? //; subst_vars; apply d=> //' }
  move=> ?? //

set_option maxHeartbeats 1600000 in
private lemma lem2 :
  (∀ a ∈ ⟪n,s'⟫, ∀ a' ∉ ⟪n,s'⟫, π a ≠ π a') := by
  move: (lem0 s z n sᵢ s' seq df dfN)=> [? ?]
  move: (disj') => d
  scase=> > /== -> ? > ?; srw if_neg //' if_pos //' if_pos //'
  scase_if=> [/==??|?]
  { scase_if=> ??; apply d=> // }
  scase_if=> [|?? //] ?; srw if_neg //' => ? //

set_option maxHeartbeats 1600000 in
private lemma lem3 :
  (∀ a ∈ ⟪n,s'⟫, ∀ a' ∈ fs, π a ≠ π a') := by
  move=> ? /lem2 /[swap] a /(_ a) /[swap]?; sapply=> //'
  scase: a=> > /[swap] _ /== //

set_option maxHeartbeats 1600000 in
private lemma lem4 :
  (∀ a ∈ ⟪n,s'⟫ ∪ fs, ∀ a' ∉ ⟪n,s'⟫ ∪ fs, π a ≠ π a') := by
  move=> a /[swap] ?; srw ?Set.mem_union=> [/lem2|/lem1] f ? <;>
  apply f=> //


omit disj seq dfN in
@[simp]
lemma disjoint_labSet :
  Disjoint ⟪l, s⟫ ⟪l', s'⟫ = (l ≠ l' ∨ Disjoint s s') := by
  sorry

-- set_option maxHeartbeats 1600000 in
-- @[simp]
-- private lemma validSubst_sUss :
--   validSubst π (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0, ss⟫) (⟪1, s⟫ ∪ ⟪0, ss⟫ : Set _) = true := by
--   unfold π'
--   move=> dj₁ dj₂ /== [l x] /== ? l' y ?
--   checkpoint (scase: l l'=> //== /[swap] []//== <;> split_ifs=> //)
--   { move=> [] // /(Set.disjoint_left.mp dj₁) // }
--   move=> /(Set.disjoint_left.mp dj₁) //
omit disj seq dfN in
lemma inj_κ : Set.InjOn κ s' := by
  move=> ?? ?? /==; srw ?if_pos //

omit disj seq dfN in
set_option maxHeartbeats 1600000 in
lemma fsubst_set_union (σ : α -> β) :
  hlocal s₁ h ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  fsubst σ (s₁ ∪ s₂) h = fsubst σ s₁ h := by
  move=> l neq !z
  srw ?fsubst ?partialInvSet
  scase: [∃ a ∈ s₁ ∪ s₂, σ a = z]=> /==
  { move=> ?; srw dif_neg // dif_neg // }
  move=> x [] xin <-
  { srw dif_pos // dif_pos /==; rotate_left
    { sby exists x }
    congr=> !y !⟨|⟩//== [] // /neq /(_ xin) // }
  srw dif_pos //; rotate_left
  { exists x=> // }
  srw /== dif_neg //==; apply l
  move=> /neq /(_ xin); sapply
  generalize heq : (choose _) = y
  shave: (y ∈ s₁ ∨ y ∈ s₂) ∧ σ y = σ x
  { srw -heq; apply choose_spec (p := fun y => (y ∈ s₁ ∨ y ∈ s₂) ∧ σ y = σ x)  }
  move=> //

omit disj seq dfN in
private lemma vsκ :
  validSubst κ s' h := by move=> ????/=; srw ?if_pos //

omit disj seq dfN in
private lemma vsπ (h : hheap α) :
  validSubst π ⟪n, s'⟫ (fsubst κ s' h) := by
  move=> [] /== ? a -> ? ? b -> ?
  srw if_neg //' if_pos //' if_pos //'

set_option maxHeartbeats 1600000 in
private lemma hE (h : hheap α) :
  hlocal s' h ->
  h = (fsubst π (⟪n, s'⟫ ∪ fs) (fsubst κ s' h)) := by
  move=> ?
  srw fsubst_set_union
  { move=> !a; scase: [a ∈ s']
    { move=> ?; srw (fsubst_local_out (s' := ⟪n,s'⟫)) //
      { move=> [m x] /== ?; apply fsubst_local_out => //
        { apply vsκ }
        srw fsubst_inE /== => ??; srw if_pos //' => [] //' }
      { apply vsπ }
      srw fsubst_inE /== => ?? -> ?
      srw if_neg //' ?if_pos //' => ? // }
    move=> ?
    shave aeq: a = π (κ a)
    { srw κ' if_pos //' }
    srw [2]aeq ?fsubst_σ //
    { apply vsκ }
    { apply vsπ }
    srw /== if_pos // }
  { move=> [m x] /== ?; apply fsubst_local_out => //
    { apply vsκ }
    srw fsubst_inE /== => ??; srw if_pos //' => [] //' }
  apply lem3=> //

lemma hsubst_πκ :
  hhlocal s' H₁ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁) = H₁ := by
  move=> lh !h !⟨![h -> ![h ->] ?? _ ]|?⟩
  { srw -hE // }
  exists (fsubst κ s' h)=> ⟨|⟨|⟩⟩
  { apply hE=> // }
  { exists h=> ⟨//|⟨//|⟩⟩; apply vsκ }
  move=> a; srw ?Set.mem_union=> [] ain b []
  { apply vsπ=> // }
  { move=> /lem3/(_ ain) /[apply] /(_ disj) /(_ seq) /(_ dfN) // }
  { move=> *; exfalso; eapply lem3=> // }
  move=> bin; srw ?fsubst_local_out //'
  { apply vsκ }
  { srw fsubst_inE /== => ??; srw if_pos
    scase: b bin=> /== // }
  { apply vsκ }
  srw fsubst_inE /== => ??; srw if_pos
  scase: a ain=> /== //


set_option maxHeartbeats 1600000 in
private lemma hsubst_H_aux :
  hhlocal s' H₁ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁ ∗ (H₂ ∘ π) ∗↑ fs) =
  (H₁ ∗ H₂ ∗↑ s) := by
  move=> ?
  move: (lem1 s z n sᵢ s' disj seq)=> ?
  move: (lem2 s z n sᵢ s' disj seq)=> ?
  move: (lem3 s z n sᵢ s' disj seq)=> ?
  move: (lem4 s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s' s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s s z n sᵢ s' disj seq)=> ?
  srw -(hsubst_hhstar (s₁ := ⟪n, s'⟫) (s₂ := fs))=> //'
  { erw [hsubst_bighstar]=> //'
    srw (hsubst_πκ s z n sᵢ s' disj seq)=> //'
    srw (ssubst_s s z n sᵢ s' disj seq)=> //'  }
  { simp => *
    move: seq disj=> -> /== //' }
  move=> ? ![h -> ??] [m a] /== ?
  srw fsubst_local_out //' fsubst_inE /==
  move=> ??; srw if_pos => //' [] //'

set_option maxHeartbeats 1600000 in
private lemma hsubst_H :
  hhlocal s' H₁ ->
  hhlocal s' H₂ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁ ∗ hsubst κ s' H₂ ∗ (H₃ ∘ π) ∗↑ fs) =
  (H₁ ∗ H₂ ∗ H₃ ∗↑ s) := by
  move=> ??
  srw -?hhstar_assoc  -(hsubst_H_aux s z n sᵢ s' disj seq df dfN)
  { srw hsubst_hhstar_same //' => ???? /==
    srw ?if_pos // }
  srw hhlocal_hhstar //


local notation "hsubst_H" => hsubst_H s z n sᵢ s' disj seq df dfN

omit disj seq dfN in
private lemma π_in_s' :
  a ∈ s' -> π (n, a) = a := by
  simp=> //

private noncomputable def ι' : Int -> α -> ℤ×α :=
  fun i a =>
    if a ∈ s' then
      (n, a)
    else if a ∈ sᵢ i then
      (i, a)
    else
      (n+1, df)

local notation "ι" => ι' n sᵢ s' df

omit dfN in
set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem5 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s' ∪ sᵢ i, ∀ a' ∉ s' ∪ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ??
  move=> ? /== [] ????
  { srw ?ι' if_pos //' }
  srw ?ι' if_neg //'
  { srw if_pos //' ?if_neg //'=> [] // }
  move=> ?; apply d=> //

omit dfN in
set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem6 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s', ∀ a' ∈ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ?? ? ? a ?;  srw ?ι' if_pos //' if_neg
  { srw ?if_pos //'; sby scase }
  move=> ?; apply (d i a)=> //

omit dfN in
set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem9 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s', ∀ a' ∉ s', ι i a ≠  ι i a' := by
  move: (disj') => d ?? ????; srw ?ι' if_pos //' if_neg //'
  scase_if=> // ? [] //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem12 i :
  z <= i ->
  i < n ->
  ∀ a ∈ sᵢ i, ∀ a' ∉ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ?? ????; srw ?ι' if_neg
  { srw if_pos //'; scase_if=> [? [] //| ? ]
    srw if_neg // => [] // }
  move=> ?; apply d=> //

omit disj seq dfN in
set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem10 i :
  validSubst (ι i) (s' ∪ sᵢ i) s' := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

omit disj seq dfN in
set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem11 i :
  validSubst (ι i) (s' ∪ sᵢ i) (sᵢ i) := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

-- Set.EqOn ht₁ ((ht₁ ∘ σ) ∘ ι) s'
omit dfN in
set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem7 i :
  z <= i ->
  i < n ->
  Set.EqOn f ((f ∘ π) ∘ ι i) (sᵢ i) := by
  move: (disj') => d ?? x ? /==
  srw ι' (if_neg (c := x ∈ s'))
  { srw (if_pos (c := x ∈ sᵢ i)) //' }
  move=> ?; apply d=> //

omit disj seq dfN in
set_option maxHeartbeats 1600000 in
private lemma lem13 i :
  ssubst (ι i) (s' ∪ sᵢ i) s' = ⟪n, s'⟫ := by
  unfold ι'
  move=> ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem10=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  exists x=> //

omit dfN in
set_option maxHeartbeats 1600000 in
private lemma lem14 i :
  z <= i ->
  i < n ->
  ssubst (ι i) (s' ∪ sᵢ i) (sᵢ i) = ⟪i, sᵢ i⟫ := by
  move: (disj') => d ?? ! [l a]
  srw fsubst_inE => /==; rotate_left
  { apply lem11=> // }
  move=> ⟨/== ? _ ?|/== -> ?⟩
  { srw ι' if_neg ?if_pos //'
    scase=> //'; move=> ?; apply d=> // }
  exists a=> //; srw ι' if_neg ?if_pos //'
  move=> ?; apply d=> //

omit dfN in
lemma fsubst_ι' i :
  z <= i ->
  i < n ->
  hlocal s' H₁ ->
  fsubst (ι i) (s' ∪ sᵢ i) H₁ = fsubst (ι i) s' H₁ := by
  move=> ???; srw fsubst_set_union //
  apply lem6=> //

lemma fsubst_κι i :
  z <= i ->
  i < n ->
  hlocal s' H₁ ->
  fsubst κ s' H₁ = fsubst (ι i) (s' ∪ sᵢ i) H₁ := by
  move=> ?? l ! [m a]
  srw (fsubst_ι' s z n) //'
  srw ?fsubst ?partialInvSet
  split_ifs <;> rename_i h₁ h₂=> /==
  { congr=> !b ! /== ?; srw if_pos // => ⟨[]|<-⟩
    { srw ι' if_pos // }
    srw ι' if_pos // }
  { exfalso; move: h₁ h₂=> /== ?? //
    srw if_pos //' => []; exists a=> ⟨//|⟩
    srw ι' if_pos // }
  exfalso; move: h₂ h₁=> /== ?? //
  srw ι' if_pos //' => []; exists a=> ⟨//|⟩
  srw if_pos //


lemma hsubst_κι i :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hsubst κ s' H₁ = hsubst (ι i) (s' ∪ sᵢ i) H₁ := by
  move=> ?? l !h ! ⟨|⟩ ![] h -> Hh ?
  { srw (fsubst_κι (i := i)) //; exists h=> ⟨//|⟨//|⟩⟩
    move=> ?; srw ?Set.mem_union=> [] ? ? [] ?
    { srw ?ι' ?if_pos // }
    { move=> *; exfalso; apply lem6 => // }
    { move=> *; exfalso; apply lem6 => // }
    srw ?(l _ Hh) //'
    { move: seq disj=> ->/== dj
      specialize dj i ?_=> //'
      srw Set.disjoint_left at dj=> // }
    move: seq disj=> -> /== => dj
    specialize dj i ?_=> //'
    srw Set.disjoint_left at dj=> // }
  srw -(fsubst_κι (i := i)) //; exists h=> ⟨//|⟨//|⟩⟩
  move=> ????; srw ?κ' ?if_pos //

attribute [-simp] π'

private lemma hsubst_H'_aux :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hsubst (ι i) (s' ∪ sᵢ i) (H₁ ∗ (H₂ ∘ (ι i)) ∗↑ sᵢ i) =
  (hsubst (ι i) (s' ∪ sᵢ i) H₁ ∗ H₂ ∗↑ ⟪i,sᵢ i⟫) := by
  move=> h h' ?
  move: (lem5 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem6 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem9 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem12 s z n sᵢ s' disj seq df dfN i h h')=> ?
  -- move: (lem7 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem10 n sᵢ s' df i)=> ?
  move: (lem11 n sᵢ s' df i)=> ?
  move: (lem13 n sᵢ s' df i)=> H₁
  move: (lem14 s z n sᵢ s' disj seq df i h h')=> h₂
  srw -(hsubst_hhstar (s₁ := s') (s₂ := sᵢ i))=> //'
  { erw [hsubst_bighstar]=> //' }
  move: seq disj=> -> /== //'

private lemma hsubst_H' :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hhlocal s' H₂ ->
  hsubst (ι i) (s' ∪ sᵢ i) (H₁ ∗ H₂ ∗ (H₃ ∘ (ι i)) ∗↑ sᵢ i) =
  (hsubst (ι i) (s' ∪ sᵢ i) H₁ ∗ hsubst (ι i) (s' ∪ sᵢ i) H₂ ∗ H₃ ∗↑ ⟪i,sᵢ i⟫) := by
  move=> ?? ??
  srw -?hhstar_assoc (hsubst_hhstar_same _ s' (s' ∪ sᵢ i)) //'
  { srw -(hsubst_H'_aux s z n sᵢ s' disj seq df) // }
  { move=> ????; srw ?ι' ?if_pos // }
  apply lem9=> //

local notation "hsubst_H'" => hsubst_H' s z n sᵢ s' disj seq df

-- private lemma hsubst_H'' (β : Type) (H₂ : β -> _) :
--   z <= i ->
--   i < n ->
--   hsubst (ι i) (s' ∪ sᵢ i) ((H₁ ∘ (ι i)) ∗↑ s' ∗ (∃ʰ x, (H₂ x ∘ (ι i)) ∗↑ s') ∗ (H₃ ∘ (ι i)) ∗↑ sᵢ i) =
--   (H₁ ∗↑ ⟪n,s'⟫ ∗ (∃ʰ x, H₂ x ∗↑ ⟪n,s'⟫) ∗ H₃ ∗↑ ⟪i,sᵢ i⟫) := by
--   move=> h h'
--   move: (lem5 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem6 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem9 z n sᵢ s' df i h h')=> ?
--   move: (lem12 s z n sᵢ s' disj seq df i h h')=> ?
--   -- move: (lem7 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem10 n sᵢ s' df i)=> ?
--   move: (lem11 n sᵢ s' df i)=> ?
--   move: (lem13 n sᵢ s' df i)=> ?
--   move: (lem14 s z n sᵢ s' disj seq df i h h')=> h₂
--   srw -hhstar_assoc [2]hhstar_comm hhstar_hhexists_l
--   srw -(hsubst_hhstar (s₁ := s') (s₂ := sᵢ i))=> //'
--   { erw [hsubst_bighstar];
--     simp_rw [bighstar_hhstar]
--     erw [hsubst_hhexists]=> //'
--     srw h₂ -hhstar_assoc [3]hhstar_comm [2]hhstar_hhexists_l;
--     congr; apply congr_arg=> !x
--     erw [hsubst_bighstar (H := (fun i_1 ↦ (H₂ x) i_1 ∗ (H₁) i_1))]
--     simp_rw [bighstar_hhstar]=> // }
--   move: seq disj=> ->; srw -disjoint_union=> /== //'

-- local notation "hsubst_H''" => hsubst_H'' s z n sᵢ s' disj seq df

omit disj seq dfN in
lemma LGTM.triple_Q_eq :
  (∀ hv, Q hv = Q' hv) ->
  LGTM.triple sht H Q = LGTM.triple sht H Q' := by
  move=> /hwp_Q_eq=> eq; srw ?LGTM.triple ?LGTM.wp eq

omit disj seq dfN in
lemma wp2_ht_eq :
  Set.EqOn ht₁ ht₁' s₁ ->
  Set.EqOn ht₂ ht₂' s₂ ->
  LGTM.wp [⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩] Q =
  LGTM.wp [⟨s₁, ht₁'⟩, ⟨s₂, ht₂'⟩] Q := by
  move=> *
  apply LGTM.wp_sht_eq=> //==

omit disj seq dfN in
lemma wp1_ht_eq :
  Set.EqOn ht₂ ht₂' s₂ ->
  LGTM.wp [⟨s₂, ht₂⟩] Q =
  LGTM.wp [⟨s₂, ht₂'⟩] Q := by
  move=> *
  apply LGTM.wp_sht_eq=> //

omit disj seq dfN in
lemma hlocal_fsubst_κ :
  hlocal s' H ->
  hlocal (⟪n, s'⟫ ∪ fs) (fsubst κ s' H) := by
  move=> hl h ?; srw fsubst_local_out //'
  { apply vsκ }
  srw fsubst_inE /== => ??; srw if_pos //'=> []//

omit disj seq dfN in
lemma hhlocal_hsubst_κ :
  hhlocal s' H ->
  hhlocal (⟪n, s'⟫ ∪ fs) (hsubst κ s' H) := by
  move=> hl h ![h -> ??]; apply hlocal_fsubst_κ=> //

set_option maxHeartbeats 1600000 in
lemma wp_for_bighop_aux (β : Type) [PartialCommMonoid val] [inst : Inhabited β]
  {c : htrm}
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  hhlocal s' H₀ ->
  (∀ i, hhlocal s' (Inv i)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun i => subst vr j (c i)⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗  R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun j => trm_for vr z n (c j)⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> lH₀ lInv lQ lgen ? eqQ gen ind *
  srw -(hsubst_H) //' LGTM.wp_Q_eq; rotate_left 2
  { move=> ?; srw -(hsubst_H) //' }
  srw -[8](ssubst_s' s z n sᵢ s' disj seq df) //'
  srw -(ssubst_s s z n sᵢ s' disj seq df) //'
  apply hsubst_wp (Q :=
    fun hv => hsubst κ s' (H₀ + ∑ j in ⟦z, n⟧, Q j (hv ∘ (j,·))) ∗ hsubst κ s' (Inv n) ∗ (R' ∘ π) ∗↑ fs)=>//'
  { apply lem3=> //' }
  { apply lem4=> //' }
  { simp=> ⟨|⟩ <;> apply hhlocal_hsubst_κ=> //' }
  { simp; omega }
  { move=> > hveq; congr! 3
    apply Finset.sum_congr (s₂ := ⟦z, n⟧)=> [//|]/==
    move=> i ?? ; apply eqQ=> //' /= ??; apply hveq=> /==; right
    exists i }
  { move=> hv; congr! 3; apply Finset.sum_congr (s₂ := ⟦z, n⟧)=> [//|]/==
    move=> i *; apply eqQ=> //' /= ??
    unfold π'=> /=; srw if_pos //' }
  srw LGTM.triple_Q_eq; rotate_left
  { move=> hv;
    rewrite [<-hsubst_hhadd_same κ s']
    rewrite [hsubst_sum_same]
    rfl
    all_goals auto
    { move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  eapply Disjoint.LGTM.wp_for_bighop (s := fs)
    (sᵢ := fun i => ⟪i, sᵢ i⟫)
    (inst := inst)
    (Inv := fun i => hsubst κ s' (Inv i))
    (Qgen := fun i v =>  hsubst κ s' $ Qgen i v)
    (Q := fun i hv =>  hsubst κ s' $ Q i (hv ∘ (i,·))) => //'
  { move=> > /== ?? hveq; apply congr_arg; apply eqQ=> //' }
  { move=> hv j /gen /(_ (fun i => hv ∘ (i, ·))) ![v H] eq
    exists v, (hsubst κ s' H);
    srw hsubst_hhstar_same //'; rotate_left
    { shave /==: hhlocal s' (Qgen j v ∗ H)
      srw -eq //= }
    { move=> ????; srw ?κ' ?if_pos // }
    srw -eq -hsubst_hhadd_same //'
    { srw hsubst_sum_same //'
      move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  { simp => *
    move: seq disj=> -> /== //' }
  { move=> /== //' }
  move=> > ?
  srw ?(hsubst_κι s z n sᵢ (i := j)) //' LGTM.wp_Q_eq; rotate_left 2
  { move=> ?; srw (hsubst_κι s z n sᵢ (i := j)) //'  }
  srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
  { move=> ?
    rewrite [hsubst_hhadd_same _ s']
    { srw -(hsubst_H') //' }
    all_goals auto
    {  move=> ????; srw ?ι' ?if_pos // }
    apply lem9=> //' }
  srw -(lem13 n sᵢ s' df) //' -(lem14 s z n sᵢ s') //'
  eapply hsubst_wp
    (Q := fun hv => ((Q j hv + Qgen j v) ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j))=> //'
  { apply lem6=> // }
  { apply lem5=> // }
  { srw ?hhlocal_hhstar=> /== ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
  { move: disj; srw seq=> /==; sapply<;> omega }
  { move=> > hveq; congr 2; apply eqQ=> //' /= ??; apply hveq=> /== //' }
  { move=> hv; congr! 2
    { apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
      move: (disj')=> //' }
    apply bighstar_eq=> /= ??
    srw ι' if_neg ?if_pos //'
    { srw π' /= if_pos //' }
    move: (disj')=> ?? //' }
  srw bighstar_eq
  { apply hhimpl_trans
    apply ind (v := v)=> //'
    srw wp2_ht_eq; apply hwp_conseq
    { move=> hv /=; ysimp }
    { move=> ? /=?; srw ι' if_pos //' π' /== if_pos //' }
    apply lem7=> // }
  move=> ??; apply Eq.symm; apply lem7=>//


lemma labSet_nonempty :
  s'.Nonempty ->
  ⟪n, s'⟫.Nonempty := by scase=> w ? ⟨⟨|⟩|//⟩

omit disj seq dfN in
private lemma κ_s' :
  ssubst κ s' s' = ⟪n, s'⟫ := by
  move=> ! [x l]; srw fsubst_inE /== => ⟨|⟩ /==
  { move=> > ?; srw if_pos // }
  move=> *; exists l=> //

set_option maxHeartbeats 1600000 in
lemma wp_while_bighop_aux [PartialCommMonoid val] [Inhabited α] (β : Type) [inst : Inhabited β]
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Bool -> Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  hhlocal s' H₀ ->
  (∀ i b, hhlocal s' (Inv i b)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv true j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' =>
          Q j hv' + Qgen j v ∗ (∃ʰ b, (Inv b (j + 1))) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Q j hv' + Qgen j v ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => hhpure (bv = fun _ => val.val_bool b) ∗ Inv b j)) ->
  (∀ b, hhimpl (Inv b n) (hhpure (b = false) ∗ Inv b n)) ->
  H₀ ∗ Inv b₀ z ∗ R ∗↑ s ==>
    LGTM.wp [⟨s', fun j => trm_while cnd c⟩, ⟨s, ht⟩]
      fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv false n ∗ R' ∗↑ s := by
  move=> lH₀ lInv lQ lgen ? eqQ gen indt indf cndN cndE
  srw -(hsubst_H) //' LGTM.wp_Q_eq; rotate_left 2
  { move=> ?; srw -(hsubst_H) //' }
  srw -[8](ssubst_s' s z n sᵢ s' disj seq df) //'
  srw -(ssubst_s s z n sᵢ s' disj seq df) //'
  apply hsubst_wp (Q :=
    fun hv => hsubst κ s' (H₀ + ∑ j in ⟦z, n⟧, Q j (hv ∘ (j,·))) ∗ hsubst κ s' (Inv false n) ∗ (R' ∘ π) ∗↑ fs)=>//'
  { apply lem3=> //' }
  { apply lem4=> //' }
  { simp=> ⟨|⟩ <;> apply hhlocal_hsubst_κ=> //' }
  { simp; omega }
  {
    move=> > hveq; congr! 3
    apply Finset.sum_congr (s₂ := ⟦z, n⟧)=> [//|]/==
    move=> i ?? ; apply eqQ=> //' /= ??; apply hveq=> /==; right
    exists i }
  { move=> hv; congr! 3; apply Finset.sum_congr (s₂ := ⟦z, n⟧)=> [//|]/==
    move=> i *; apply eqQ=> //' /= ??
    unfold π'=> /=; srw if_pos //' }
  srw LGTM.triple_Q_eq; rotate_left
  { move=> hv;
    rewrite [<-hsubst_hhadd_same κ s']
    rewrite [hsubst_sum_same]
    rfl
    all_goals auto
    { move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  eapply Disjoint.LGTM.wp_while_bighop (s := fs)
    (sᵢ := fun i => ⟪i, sᵢ i⟫)
    (inst := inst)
    (Inv := fun b i => hsubst κ s' (Inv b i))
    (Qgen := fun i v =>  hsubst κ s' $ Qgen i v)
    (Q := fun i hv =>  hsubst κ s' $ Q i (hv ∘ (i,·))) => //'
  { move=> > /== ?? hveq; apply congr_arg; apply eqQ=> //' }
  {
    move=> hv j /gen /(_ (fun i => hv ∘ (i, ·))) ![v H] eq
    exists v, (hsubst κ s' H);
    srw hsubst_hhstar_same //'; rotate_left
    { shave /==: hhlocal s' (Qgen j v ∗ H)
      srw -eq //= }
    { move=> ????; srw ?κ' ?if_pos // }
    srw -eq -hsubst_hhadd_same //'
    { srw hsubst_sum_same //'
      move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  {
    simp => *
    move: seq disj=> -> /== //' }
  { move=> /== //' }
  {
    move=> > ?
    rewrite [<-hsubst_hhexists]
    srw ?(hsubst_κι s z n sᵢ (i := j)) //' LGTM.wp_Q_eq; rotate_left 2
    { move=> ?; srw (hsubst_κι s z n sᵢ (i := j)) //'  }
    srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
    { move=> ?
      rewrite [hsubst_hhadd_same _ s']
      { srw -(hsubst_H') //' }
      all_goals auto
      {  move=> ????; srw ?ι' ?if_pos // }
      apply lem9=> //' }
    srw -(lem13 n sᵢ s' df) //' -(lem14 s z n sᵢ s' _ _ df) //'
    eapply hsubst_wp
      (Q := fun hv => ((Q j hv + Qgen j v) ∗ (∃ʰ b, Inv b (j+1)) ∗ R' ∗↑ sᵢ j))=> //'
    { apply lem6=> // }
    { apply lem5=> // }
    { srw ?hhlocal_hhstar=> /== ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
    { move: disj; srw seq=> /==; sapply<;> omega }
    { move=> > hveq; congr 2; apply eqQ=> //' /= ??; apply hveq=> /== //' }
    { move=> hv; congr! 2
      { apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
        move: (disj')=> //' }
      apply bighstar_eq=> /= ??
      srw ι' if_neg ?if_pos //'
      { srw π' /= if_pos //' }
      move: (disj')=> ?? //' }
    srw bighstar_eq
    { apply hhimpl_trans
      apply indt (v := v)=> //'
      srw wp2_ht_eq; apply hwp_conseq
      { move=> hv /=; ysimp }
      { move=> ? //' }
      apply lem7=> // }
    move=> ??; apply Eq.symm; apply lem7=>// }
  {
    move=> > ?
    srw ?(hsubst_κι s z n sᵢ (i := j)) //' LGTM.wp_Q_eq; rotate_left 2
    { move=> ?; srw (hsubst_κι s z n sᵢ (i := j)) //'  }
    srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
    { move=> ?
      rewrite [hsubst_hhadd_same _ s']
      { srw -(hsubst_H') //' }
      all_goals auto
      {  move=> ????; srw ?ι' ?if_pos // }
      apply lem9=> //' }
    srw -(lem14 s z n sᵢ s' _ _ df) //'
    eapply hsubst_wp1
      (s₁ := sᵢ j)
      (s₂ := s')
      (Q := fun hv => ((Q j hv + Qgen j v) ∗ (Inv false (j+1)) ∗ R' ∗↑ sᵢ j))=> //'
    { move=> ? /[swap] ? /[swap] ? /[swap] /(@Eq.symm _ _ _) /[swap]
      apply lem6=> // }
    { apply lem5=> // }
    { srw ?hhlocal_hhstar=> /== ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
    { srw Set.union_comm }
    { srw disjoint_comm
      move: disj; srw seq=> /==; sapply<;> omega }
    { move=> > hveq; congr 2; apply eqQ=> //' }
    {
      move=> hv; congr! 2
      { apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
        move: (disj')=> //' }
      apply bighstar_eq=> /= ??
      srw ι' if_neg ?if_pos //'
      { srw π' /= if_pos //' }
      move: (disj')=> ?? //' }
    srw bighstar_eq
    { apply hhimpl_trans
      apply indf (v := v)=> //'
      srw wp1_ht_eq; apply hwp_conseq
      { move=> hv /=; ysimp }
      apply lem7=> // }
    move=> ??; apply Eq.symm; apply lem7=>// }
  { move=> > *; srw -(κ_s' (df := df))
    srw -hwp_equiv; apply hhimpl_trans
    { apply hsubst_hwp (ht := fun _ => cnd) (Q := fun v => ⌜∀ x ∈ s', v x = b⌝ ∗ Inv b j)=> //'
      { move=> > eq *; ysimp
        { ysimp=> *; srw eq //' }
        move=> *; srw -eq //' }
      apply hhimpl_trans; apply cndN=> //'
      apply hwp_conseq'=> v /=; ysimp[v]=> ?? //' }
    apply hwp_conseq'=> v /=; srw hsubst_hhpure'
    ysimp[(fun x => val.val_bool b)]=> eq; funext ⟨x, l⟩=> /==
    srw κ_s' /== => -> /[dup] ? /eq <-; sby srw if_pos }
  move=> ?; srw -hsubst_hhpure'
  apply hsubst_hhimpl=> //'

end
end ForLoopAux

variable (z n : ℤ)
variable (sᵢ : ℤ -> Set α)
variable (s' : Set α)
variable (disj : Disjoint s' s)
variable (seq: s = ∑ i in ⟦z, n⟧, sᵢ i)

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

section
include disj seq

omit disj in
private lemma lem_s' [Inhabited α] :
  z <= i ->
  i < n ->
  ssubst some (s' ∪ s) s' =
  ssubst some (s' ∪ sᵢ i) s' := by
  move=> ?? !x /== ⟨|⟩ /==//

omit disj in
private lemma lem_ss' [Inhabited α] :
  ssubst some (s' ∪ s) s' =
  ssubst some s' s' := by
  move=> !x /== ⟨|⟩ /==//

omit disj in
private lemma lem_s [Inhabited α] :
  z <= i ->
  i < n ->
  ssubst some (s' ∪ s) (sᵢ i) =
  ssubst some (s' ∪ sᵢ i) (sᵢ i) := by
  move=> ?? !x /== ⟨|⟩ /==// ? -> _ ? ⟨|⟨//|⟨|//⟩⟩⟩
  right; srw seq /==; exists i=> //'

omit disj in
private lemma lem_fsubst [Inhabited α] :
  z <= i ->
  i < n ->
  hlocal s' H ->
  fsubst some (s' ∪ s) H = fsubst some (s' ∪ sᵢ i) H := by
  move=> *;
  apply Eq.symm; apply fsubst_subset_set_local=> /==//
  { srw seq; apply Set.subset_union_of_subset_right=> ? /== ?
    exists i }
  apply hhlocal_subset s'=> //

omit disj seq in
private lemma lem_fsubst' [Inhabited α] :
  hlocal s' H ->
  fsubst some (s' ∪ s) H = fsubst some s' H := by
  move=> *;
  apply Eq.symm; apply fsubst_subset_set_local=> /==//

omit disj in
private lemma lem_hsubst [Inhabited α] :
  z <= i ->
  i < n ->
  hhlocal s' H ->
  hsubst some (s' ∪ s) H = hsubst some (s' ∪ sᵢ i) H := by
  move=> * !h ! ⟨|⟩ ![h -> ? _] ⟨//|⟨|⟨//|?//⟩⟩⟩ <;> srw (lem_fsubst s z n (i := i)) //

omit disj seq in
private lemma lem_hsubst' [Inhabited α] :
  hhlocal s' H ->
  hsubst some (s' ∪ s) H = hsubst some (s') H := by
  move=> * !h ! ⟨|⟩ ![h -> ? _] ⟨//|⟨|⟨//|?//⟩⟩⟩ <;> srw (lem_fsubst' s) //

omit seq disj in
@[simp]
lemma inj_some : Set.InjOn some s' = true := by move=> /== ? * //

set_option maxHeartbeats 1600000 in
lemma wp_for_bighop [Inhabited α] [PartialCommMonoid val] (β : Type)  [inst:Inhabited β]
  (Q : Int -> hval -> hhProp)
  {c : htrm}
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  z <= n ->
  hhlocal s' H₀ ->
  (∀ i, hhlocal s' (Inv i)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun i => subst vr j (c i)⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗  R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun j => trm_for vr z n (c j)⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> L ???? eqQ gen *
  eapply wp_hsubst_some=> //'
  { simp=> ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
  { move=> ? /== ⟨⟨|⟩|⟩
    { apply hhlocal_subset s'=> //' }
    { move=> *; apply hhlocal_subset s'=> //' }
    apply hhlocal_subset s'=> //' }
  srw hsubst_some_hhstar' //' ForLoopAux.LGTM.triple_Q_eq;  rotate_left
  {  move=> hv;
     rewrite [hsubst_some_hhstar']
     rewrite [<-hsubst_hhadd_same]
     rewrite [hsubst_sum_same]
     rfl=> //'
     { move=> * [] //' }
     move=> * [] //' }
  srw Function.comp /=
  apply ForLoopAux.wp_for_bighop_aux _ _ _ (c := (c ·.get!))
    (fun i => ssubst some (s' ∪ s) $ sᵢ i) (ssubst some (s' ∪ s) s')
    (df := none)
    (Qgen := fun i v => hsubst some (s' ∪ s) (Qgen i v))
    (Inv := fun i => hsubst some (s' ∪ s) (Inv i))
    (inst := inst)
    (Q := fun j hv => hsubst some (s' ∪ s) (Q j (hv ∘ some)))=> //'
  { apply hhlocal_some=> //' }
  { move=> ?; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> j hv₁ hv₂ ? hveq; congr! 1; apply eqQ=> //'
    move=> x ?; apply hveq=> //' /== ⟨|//'⟩; right; srw seq /==; exists j=> //' }
  { move=> > hj; scase!: (gen (hv · ∘ some) j hj)=> v H eq ⟨//|⟩
    exists hsubst some (s' ∪ s) H
    srw hsubst_hhstar_same //'
    { srw -eq -hsubst_hhadd_same //'
      { srw hsubst_sum_same //' => * [] //' }
      move=> * [] //' }
    { shave/==: hhlocal s' (Qgen j v ∗ H)
      srw -eq ?hhProp_add_def //' }
    move=> * [] //' }
  { move=> > ?
    shave ?: Disjoint s' (sᵢ j)
    { move: seq disj=> -> /== // }
    srw (lem_s' s z n sᵢ) //' (lem_s s z n sᵢ) //'
    srw ?(lem_hsubst s z n sᵢ s' (i := j)) //' -hsubst_some_hhstar' //'
    srw LGTM.wp_Q_eq; rotate_left 2
    { move=> hv
      rewrite [lem_hsubst s z n sᵢ s' (i := j)]
      rewrite [hsubst_hhadd_same]
      { srw -hsubst_some_hhstar' //' }
      all_goals auto
      move=> * [] //' }
    apply hsubst_wp=> //' /==
    { move=> ??? /[swap] <-
      apply Set.disjoint_left.mp=> //' }
    { move=> * [] // }
    { constructor <;> apply hhlocal_subset s'=> //' }
    move=> > hveq ?; congr; apply eqQ=> //'  }
  { apply ssubst_some_disjoint=> // }
  srw [2]seq; clear *-L
  move: n; apply Int.le_induction
  { srw Finset.Ico_self /== => ! // }
  move=> n ? ih; srw sum_Ico_predr /== //' ssubst_some_union ih
  srw [2]sum_Ico_predr /== //

set_option maxHeartbeats 1600000 in
lemma wp_while_bighop [Inhabited α] [PartialCommMonoid val] (β : Type)  [inst:Inhabited β]
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Bool -> Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  z <= n ->
  hhlocal s' H₀ ->
  (∀ i b, hhlocal s' (Inv i b)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv true j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' =>
          Q j hv' + Qgen j v ∗ (∃ʰ b, (Inv b (j + 1))) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Q j hv' + Qgen j v ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => hhpure (bv = fun _ => val.val_bool b) ∗ Inv b j)) ->
  (∀ b, hhimpl (Inv b n) (hhpure (b = false) ∗ Inv b n)) ->
  H₀ ∗ Inv b₀ z ∗ R ∗↑ s ==>
    LGTM.wp [⟨s', fun j => trm_while cnd c⟩, ⟨s, ht⟩]
      fun hv => H₀ + (∑ j in ⟦z, n⟧, Q j hv) ∗ Inv false n ∗ R' ∗↑ s := by
  move=> L ???? eqQ gen ?? cndN cndE
  eapply wp_hsubst_some=> //'
  { simp=> ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
  { move=> ? /== ⟨⟨|⟩|⟩
    { apply hhlocal_subset s'=> //' }
    { move=> *; apply hhlocal_subset s'=> //' }
    apply hhlocal_subset s'=> //' }
  srw hsubst_some_hhstar' //' ForLoopAux.LGTM.triple_Q_eq;  rotate_left
  {  move=> hv;
     rewrite [hsubst_some_hhstar']
     rewrite [<-hsubst_hhadd_same]
     rewrite [hsubst_sum_same]
     rfl=> //'
     { move=> * [] //' }
     move=> * [] //' }
  srw Function.comp /=
  apply ForLoopAux.wp_while_bighop_aux _ _ _ --(c := (c ·.get!))
    (fun i => ssubst some (s' ∪ s) $ sᵢ i) (ssubst some (s' ∪ s) s')
    (df := none)
    (Qgen := fun i v => hsubst some (s' ∪ s) (Qgen i v))
    (Inv := fun b i => hsubst some (s' ∪ s) (Inv b i))
    (inst := inst)
    (Q := fun j hv => hsubst some (s' ∪ s) (Q j (hv ∘ some)))=> //'
  { apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> j hv₁ hv₂ ? hveq; congr! 1; apply eqQ=> //'
    move=> x ?; apply hveq=> //' /== ⟨|//'⟩; right; srw seq /==; exists j=> //' }
  { move=> > hj; scase!: (gen (hv · ∘ some) j hj)=> v H eq ⟨//|⟩
    exists hsubst some (s' ∪ s) H
    srw hsubst_hhstar_same //'
    { srw -eq -hsubst_hhadd_same //'
      { srw hsubst_sum_same //' => * [] //' }
      move=> * [] //' }
    { shave/==: hhlocal s' (Qgen j v ∗ H)
      srw -eq ?hhProp_add_def //' }
    move=> * [] //' }
  { move=> > ?
    shave ?: Disjoint s' (sᵢ j)
    { move: seq disj=> -> /== // }
    srw (lem_s' s z n sᵢ) //' (lem_s s z n sᵢ) //' -hsubst_hhexists
    srw ?(lem_hsubst s z n sᵢ s' (i := j)) //' -hsubst_some_hhstar' //'
    srw LGTM.wp_Q_eq; rotate_left 2
    { move=> hv
      rewrite [lem_hsubst s z n sᵢ s' (i := j)]
      rewrite [hsubst_hhadd_same]
      { srw -hsubst_some_hhstar' //' }
      all_goals auto
      move=> * [] //' }
    apply hsubst_wp=> //' /==
    { move=> ??? /[swap] <-
      apply Set.disjoint_left.mp=> //' }
    { move=> * [] // }
    { constructor <;> apply hhlocal_subset s'=> //' }
    move=> > hveq ?; congr; apply eqQ=> //'  }
  { move=> > ?
    shave ?: Disjoint s' (sᵢ j)
    { move: seq disj=> -> /== // }
    srw (lem_s s z n sᵢ) //'
    srw ?(lem_hsubst s z n sᵢ s' (i := j)) //' -hsubst_some_hhstar' //'
    srw LGTM.wp_Q_eq; rotate_left 2
    { move=> hv
      rewrite [lem_hsubst s z n sᵢ s' (i := j)]
      rewrite [hsubst_hhadd_same]
      { srw -hsubst_some_hhstar' //' }
      all_goals auto
      move=> * [] //' }
    eapply hsubst_wp1 (s₁ := sᵢ j) (s₂ := s'); rotate_right=> //' /==
    { move=> ? ain ??; move: ain=> /[swap] ->
      apply Set.disjoint_left.mp=> //' }
    { move=> * [] // }
    { constructor <;> apply hhlocal_subset s'=> //' }
    { srw Set.union_comm }
    move=> > hveq; congr; apply eqQ=> //' }
  { move=> > *; srw ?(lem_ss' s z n sᵢ) //' lem_hsubst' //'
    srw -hwp_equiv; apply hhimpl_trans
    { apply hsubst_hwp (ht := fun _ => cnd) (Q := fun v => ⌜∀ x ∈ s', v x = b⌝ ∗ Inv b j)=> //'
      { move=> * [] // }
      { move=> > eq *; ysimp
        { ysimp=> *; srw eq //' }
        move=> *; srw -eq //' }
      apply hhimpl_trans; apply cndN=> //'
      apply hwp_conseq'=> v /=; ysimp[v]=> ?? //' }
    apply hwp_conseq'=> v /=; srw hsubst_hhpure'
    ysimp[(fun x => val.val_bool b)]=> eq; funext x=> /== //' }
  { move=> ?; srw -hsubst_hhpure'
    apply hsubst_hhimpl=> //' }
  { apply ssubst_some_disjoint=> // }
  srw [2]seq; clear *-L
  move: n; apply Int.le_induction
  { srw Finset.Ico_self /== => ! // }
  move=> n ? ih; srw sum_Ico_predr /== //' ssubst_some_union ih
  srw [2]sum_Ico_predr /== //
end

end
