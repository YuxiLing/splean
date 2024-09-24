import Mathlib.Data.Finmap
import Mathlib.Data.List.Indexes

-- lemmas about big operators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

-- lemmas about intervals
import Mathlib.Data.Int.Interval

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog
import Lgtm.Unary.ArraysFun

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.Arrays

section

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

attribute [simp] hseg



def hharrayFun (f : ℤ -> val)  (n : ℕ) (p : α -> loc) : hhProp :=
  bighstar s (fun i => harrayFun f n (p i))

lemma hharrayFunE (f : ℤ -> val) :
  hharrayFun s f n p = hharray s (@List.ofFn _ n (f ·.val)) p := by
  rfl


attribute [-simp] Int.natCast_natAbs in
lemma hharrayFun_eq_hhadd [PartialCommMonoid val] :
  hharrayFun s f n p =
    (p i ~⟨i in s⟩~> val.val_int n) +
    ∑ i in [[(0 : ℤ), ↑n]], (p j + 1 + i.natAbs ~⟨j in s⟩~> f i) := by
  srw hharrayFunE hharray_eq_hhadd; congr! 1
  { congr!=> // }
  apply Finset.sum_congr=> //== ???; congr! 2
  srw getElem!_pos //== <;> try omega
  erw [List.getElem_ofFn]=> /==; congr; omega

notation "arr(" p "⟨" s "⟩, " x " in " n " => " f ")" => hharrayFun s (fun x => f) n (fun _ => p)


lemma hharrayFun_hhadd_sum [PartialCommMonoid val] (n : ℕ) (l : ℤ) (v : Int -> val) :
  (∀ x, PartialCommMonoid.valid (f x)) ->
  (∀ x, PartialCommMonoid.valid (v x)) ->
  0 <= l ->
  l <= n ->
  hharrayFun s f n p +
    ∑ i in [[0, l]], (p j + 1 + i.natAbs ~⟨j in s⟩~> v i) =
    hharrayFun s (fun i => if i < l then f i + v i else f i) n p := by
  move=> ?? ??; srw hharrayFun_eq_hhadd /== add_assoc
  srw -(Finset.Ico_union_Ico_eq_Ico (b := l)) //
  srw ?Finset.sum_union
  { srw add_assoc [2]add_comm add_assoc  -Finset.sum_add_distrib
    srw [2](Finset.sum_congr rfl); rotate_left
    { move=> ??; srw hhadd_hhsingle_gen // }
    srw hharrayFun_eq_hhadd; congr 1
    srw -[3](Finset.Ico_union_Ico_eq_Ico (b := l)) // Finset.sum_union
    { srw [2]add_comm; congr 1 <;> apply Finset.sum_congr=> // i /== ??
      { srw if_neg // }
      srw if_pos //; congr! 2; srw add_comm }
    srw Finset.disjoint_left=> /==; omega }
  srw Finset.disjoint_left=> /==; omega

open EmptyPCM in
lemma harrayFun_chip_off (i : ℤ) (n : ℕ) :
  0 <= i -> i < n ->
  ∃ H, hharrayFun s f n p = (p j + 1 + i.natAbs ~⟨j in s⟩~> f i) ∗ H := by
  move=> ??; econstructor
  srw hharrayFun_eq_hhadd hhaddE
  srw -(Finset.sdiff_union_of_subset (α := ℤ) (s₁ := {i}) (s₂ := [[0, ↑n]])) //
  srw Finset.sum_union //==; ysimp; ysimp

end
