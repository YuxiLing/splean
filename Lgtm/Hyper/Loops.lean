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

section ForLoop

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
  | `(ssr_triv) => `(omega)

lemma LGTM.wp_for_aux
  (z i n : Int)
  (Inv : Int -> hval -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= i ∧ i <= n ->
  (∀ j hv₁ hv₂, i <= j ∧ j <= n -> (∀ x, x ∉ s' -> hv₁ x = hv₂ x) -> Inv j hv₁ = Inv j hv₂) ->
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
    srw Heq=> // }
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


end ForLoop
