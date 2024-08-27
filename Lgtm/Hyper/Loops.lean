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

import Lgtm.Unary.Util
import Lgtm.Unary.WP

import Lean

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP

open Classical trm val prim
open SetSemiring

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

-- open BigOperators

instance : AddCommMonoid (Set α) := SetSemiring.instAddCommMonoid



-- abbrev interval (z n : Int) : Finset Int := Finset.Ico z n

notation "[[" z ", " n "]]" => Finset.Ico z n

lemma sum_Ico_succl [AddCommMonoid M] (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i in [[i, j]], f i = f i + ∑ i in [[i+1, j]], f i := by sorry

lemma sum_Ico_predr [AddCommMonoid M] (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i in [[i, j]], f i = (∑ i in [[i, j - 1]], f i) + f (j -1) := by sorry


lemma disjoint_union (sᵢ : β -> Set α)  :
  (∀ x ∈ fs, Disjoint s (sᵢ x)) =
  Disjoint s (∑ i in fs, sᵢ i) := by sorry

lemma mem_union (sᵢ : β -> Set α) :
  (x ∈ ∑ i ∈ fs, sᵢ i) = ∃ i ∈ fs, x ∈ sᵢ i := by sorry

@[simp]
lemma plusE (s₁ s₂ : Set α) : s₁ + s₂ = s₁ ∪ s₂ := by rfl
@[simp]
lemma zE  : (0 : Set α) = ∅ := by rfl


-- lemma hwp_for_aux
--   (z i n : Int)
--   (H : Int -> hval -> hhProp)
--   (sᵢ : Int -> Set α)
--   (ht : htrm) :
--   z <= i ∧ i < n ->
--   (∀ j hv₁ hv₂, i <= j ∧ j <= n -> (∀ x, x ∈ (⋃ i ∈ [[Z, j]], sᵢ i) -> hv₁ x = hv₂ x) -> H j hv₁ = H j hv₂) ->
--   (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
--   s = (⋃ i ∈ [[i, n]], sᵢ i) ->
--   Disjoint s' s ->
--   (∀ x, x ∈ s' -> ht x = trm_for vr i n c) ->
--   (∀ j hv, z <= j ∧ j < n ->
--      H j hv ==>
--        hwp (s' ∪ sᵢ j)
--            ((fun _ => subst vr j c) ∪_s' ht)
--            (fun hv' => H (j + 1) (hv ∪_(⋃ i ∈ [[Z, j]], sᵢ i) hv'))) ->
--   H i hv₀ ==>
--     hwp (s' ∪ s)
--          ht
--          (fun hv => H N (hv₀ ∪_(⋃ i ∈ [[Z, i]], sᵢ i) hv)) := by
-- set_option maxHeartbeats 800000 in

macro_rules
  | `(tactic| ssr_triv) => `(tactic| omega)

section ForLoop

lemma LGTM.wp_for_aux
  (z i n : Int)
  (Inv : Int -> hval -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= i ∧ i <= n ->
  (∀ j hv₁ hv₂, i <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  s = ∑ i in [[i, n]], sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
     Inv j hv ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' => Inv (j + 1) (hv ∪_(∑ i in [[z, j]], sᵢ i) hv'))) ->
  Inv i hv₀ ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr i n c⟩, ⟨s, ht⟩]
         (fun hv => Inv n (hv₀ ∪_(∑ i in [[z, i]], sᵢ i) hv)) := by
  move=> iin Heq dij seq sij' ind
  shave H: i <= n; omega; move: i H hv₀ s seq iin Heq
  apply Int.le_induction_down
  { move=> > ?-> ? Heq
    srw Finset.Ico_self /== wp_cons /=
    ychange hwp_for'=> /==
    srw wp /== hwp0_dep; ysimp[hv₀]
    apply Heq=> // }
  move=> i ? ih hv₀ ? sij' seq ? Heq
  srw wp_cons /=; ychange hwp_for=> /==
  { omega }
  { sdone }
  srw -(wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ (_ ∪__ x)))
  srw sum_Ico_succl
  ychange wp_align_step
  { srw -disjoint_union at sij'; apply sij'=> /==; omega }
  { move: sij'; srw sum_Ico_succl /==; omega }
  { simp; srw -disjoint_union=> /== *; apply dij=> /== <;> omega }
  { omega }
  { simp=> ⟨|⟩
    { srw -disjoint_union at sij'; apply sij'=> /==; omega }
    move: sij'; srw sum_Ico_succl /==; omega }
  { omega }
  ychange ind
  { simpNums; omega }
  apply hwp_conseq=> hv /==
  -- scase: [i = n]=> [?|->]
  ychange (ih (s := ∑ i ∈ [[i, n]], sᵢ i)) <;> try trivial
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
lemma LGTM.wp_for (Inv : Int -> hval -> hhProp) (sᵢ : Int -> Set α) (ht : htrm) :
   (z <= n) ->
   (∀ j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
   Disjoint s' s ->
   (∀ j hv, z <= j ∧ j < n ->
      Inv j hv ==>
        LGTM.wp [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩] (fun hv' => Inv (j + 1) (hv' ∪_(sᵢ j) hv))) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (s = ∑ i in [[z, n]], sᵢ i) ->
  (P ==> Inv z hv₀) ->
  (Inv n ===> Q) ->
   P ==> LGTM.wp [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩] Q := by
     move=> ? inveq disj ind dij seq pimpl implq
     ychange pimpl
     ychange LGTM.wp_conseq; apply implq
     ychange (LGTM.wp_for_aux (sᵢ := sᵢ) (i := z) (z := z) (n := n))=> //
     rotate_right
     { sby apply wp_conseq=> ? }
     move=> > ?; ychange ind=> //
     apply hwp_conseq'=> hv' /==
     ysimp[hv]; apply inveq=> //
     move=> x /==
     srw -disjoint_union at disj
     split_ifs=> //
     case pos h₁ h₂=>
       move: h₂ h₁; srw mem_union=> ![]/== j' *
       shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
       sby apply dij=> /==

end ForLoop

section WhileLoop

set_option maxHeartbeats 1600000 in
lemma LGTM.wp_while_aux_false (Inv : Int -> hval -> hhProp)  (sᵢ : Int -> Set α) :
  (∀ j hv, z <= j ∧ j < n ->
    Inv j hv ==>
      LGTM.wp
        [⟨sᵢ j, ht⟩]
          (fun hv' => Inv (j+1) (hv ∪_(∑ i in [[z, j]], sᵢ i) hv'))) ->
  (z <= i ∧ i <= n) ->
  (∀ j hv₁ hv₂, z <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ ==> Inv j hv₂) ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (s = ∑ i in [[i, n]], sᵢ i) ->
  Disjoint s' s ->
  Inv i hv₀ ==>
    LGTM.wp
         [⟨s, ht⟩]
         (fun hv => Inv n (hv₀ ∪_(∑ i in [[z, i]], sᵢ i) hv) ) := by
    move=> ind []L₁ L₂ Inveq disj; move: i L₂ L₁ s hv₀
    apply Int.le_induction_down
    { move=> ?? hv₀ ->/==; srw wp /== hwp0_dep; ysimp[hv₀]
      apply Inveq=> // }
    move=> j ? ih ? s hv₀ ->
    srw sum_Ico_succl /==; intros _ dij=> //
    srw -(fun_insert_ff (s := sᵢ (j - 1)) (f := ht))
    srw -wp_unfold_first
    ychange ind
    { sby simpNums }
    { srw -disjoint_union=> /== *; apply disj=> /== <;> omega }
    simp; srw ?wp_cons /=; apply hwp_conseq
    { move=> hv /=; srw wp /== hwp0_dep; ysimp=> ?
      ychange ih <;> try trivial
      { omega }
      apply hwp_conseq=> ?; apply Inveq
      { sdone }
      srw [2]sum_Ico_predr /==; intros
      split_ifs=> // }
    { srw /== -disjoint_union=> /== *; apply disj=> /== <;> omega }
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
  s = ∑ i in [[i, n]], sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv true j hv ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' => h∃ b, Inv b (j + 1) (hv ∪_(∑ i in [[z, j]], sᵢ i) hv'))) ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv false j hv ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Inv false (j + 1) (hv ∪_(∑ i in [[z, j]], sᵢ i) hv'))) ->
  (∀ j b hv, z <= j ∧ j <= n ->
    Inv b j hv ==> hwp s' (fun _ => cnd) (fun bv => ⌜bv = fun _ => val.val_bool b⌝ ∗ Inv b j hv)) ->
  (∀ hv b, Inv b n hv ==> ⌜b = false⌝ ∗ Inv b n hv) ->
  Inv b₀ i hv₀ ==>
    LGTM.wp
         [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩]
         (fun hv => Inv false n (hv₀ ∪_(∑ i in [[z, i]], sᵢ i) hv)) := by
    move=> []L₁ L₂ Inveq disj seq dij indt indf cndE cndn
    scase: b₀
    { clear indt
      srw wp_cons /=; ychange hwp_while=> //
      ychange cndE=> //; apply hwp_conseq=> hv /=
      ysimp; ychange hwp_if
      apply htriple_val
      apply hhimpl_trans; apply LGTM.wp_while_aux_false=> //
      apply hwp_conseq=> ? /=; apply Inveq=> // }
    move: i L₂ L₁ s hv₀  seq
    apply Int.le_induction_down
    { move=> ???? ->/==; ychange cndn=> // }
    move=> j ? ind ? s dij hv₀ ?
    srw wp_cons /=; ychange hwp_while=> //
    -- { sorry }
    ychange cndE
    { sby simpNums }
    apply hwp_conseq=> hv /=
    ysimp; ychange hwp_if
    srw -(wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ _ (_ ∪__ x)))
    srw sum_Ico_succl
    ychange wp_align_step
    { srw -disjoint_union at dij; apply dij=> /==; omega }
    { move: dij; srw sum_Ico_succl /==; omega }
    { simp; srw -disjoint_union=> /== *; apply disj=> /== <;> omega }
    { omega }
    { simp=> ⟨|⟩
      { srw -disjoint_union at dij; apply dij=> /==; omega }
      move: dij; srw sum_Ico_succl /==; omega }
    { omega }
    ychange indt
    { simpNums; omega }
    apply hwp_conseq=> hv /==
    shave ?: Disjoint s' (∑ i ∈ [[j, n]], sᵢ i)
    { move: dij; srw sum_Ico_succl /==; omega }
    ysimp=> []
    { srw wp_cons /=;
      apply hhimpl_trans_r; apply hwp_while=> //
      apply hhimpl_trans; apply cndE
      { omega }
      apply hwp_conseq=> hv /=
      apply hhimpl_hstar_hhpure_l=> -> /=
      apply hhimpl_trans_r; apply hwp_if=> /=
      apply htriple_val
      apply hhimpl_trans; apply LGTM.wp_while_aux_false <;> try trivial
      { omega }
      { sdone }
      apply hwp_conseq=> ? /=; apply Inveq=> //==
      srw sum_Ico_predr /==; intros
      split_ifs=> // }
    apply hhimpl_trans; apply (ind (s := ∑ i in [[j, n]], sᵢ i)) <;> try trivial
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
  s = ∑ i in [[z, n]], sᵢ i ->
  Disjoint s' s ->
  (∀ j hv, z <= j ∧ j < n ->
    Inv true j hv ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          (fun hv' => h∃ b, Inv b (j + 1) (hv' ∪_(sᵢ j) hv))) ->
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
  P ==> LGTM.wp [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩] Q := by
    move=> ? inveq disj seq dij indt indf cndE cndn pimpl implq
    ychange pimpl
    ychange LGTM.wp_conseq; apply implq
    ychange (LGTM.wp_while_aux (sᵢ := sᵢ) (n := n) (z := z)) <;> try trivial
    rotate_right
    { sby apply wp_conseq=> ? }
    { move=> > ?; ychange indt=> //
      apply hwp_conseq'=> hv' /==
      ypull=> b
      ysimp[hv, b]; apply inveq=> //
      move=> x /==
      srw -disjoint_union at dij
      split_ifs=> //
      case pos h₁ h₂=>
        move: h₂ h₁; srw mem_union=> ![]/== j' *
        shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
        sby apply disj=> /== }
    move=> > ?; ychange indf=> //
    apply hwp_conseq'=> hv' /==
    ysimp[hv]; apply inveq=> //
    move=> x /==
    srw -disjoint_union at dij
    split_ifs=> //
    case pos h₁ h₂=>
      move: h₂ h₁; srw mem_union=> ![]/== j' *
      shave/Set.disjoint_left//: Disjoint (sᵢ j) (sᵢ j')
      sby apply disj=> /==


end WhileLoop
