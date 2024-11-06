import Mathlib.Data.Finmap
import Mathlib.Data.List.Indexes

-- lemmas about big operators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

-- lemmas about intervals
import Mathlib.Data.Int.Interval

import Lgtm.Common.Heap

import Lgtm.Common.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog
import Lgtm.Unary.Arrays

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog

section

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

attribute [simp] hseg

open EmptyPCM in
lemma hseg_eq_bighstar :
  j >= 0 ->
  hseg L p j = ∑ i in ⟦0, ↑L.length⟧, (p + 1 + (j + i).natAbs ~~> L[i]!) := by
  elim: L j=> //== v l /[swap] > /[swap]? ->; rotate_left
  { omega }
  srw [2]sum_Ico_succl //==; erw [<-sum_Ico_succlr _ 0 _, hcell]
  xsimp
  { unfold getElem! instGetElem?OfGetElemOfDecidable=> /==
    unfold decidableGetElem?=> /== // }
  { xsimp=> //
    { unfold getElem! instGetElem?OfGetElemOfDecidable=> /==
      unfold decidableGetElem?=> /== // }
    srw Finset.sum_congr=> // ??
    rename_i i iin
    simp at iin
    shave ?: i < l.length
    { omega }
    shave ?: i.natAbs < l.length
    { omega }
    shave ?: (i + 1).natAbs < l.length + 1
    { omega }
    congr! 1;
    { congr 2; omega }
    unfold getElem! instGetElem?OfGetElemOfDecidable=> /==
    unfold decidableGetElem?=> /== //==
    srw ?dif_pos //
    srw instGetElemListIntLtNatNatAbsLength_lgtm /==
    srw -?getElem!_pos //== nat_abs_succ // }
  move=> _
  srw Finset.sum_congr=> // ??
  rename_i i iin
  simp at iin
  shave ?: i < l.length
  { omega }
  shave ?: i.natAbs < l.length
  { omega }
  shave ?: (i + 1).natAbs < l.length + 1
  { omega }
  congr! 1;
  { congr 2; omega }
  unfold getElem! instGetElem?OfGetElemOfDecidable=> /==
  unfold decidableGetElem?=> /== //==
  srw ?dif_pos //
  srw instGetElemListIntLtNatNatAbsLength_lgtm /==
  srw -?getElem!_pos //== nat_abs_succ //


def hharray (L :List val) (p : α -> loc) : hhProp :=
  bighstar s (fun i => harray L (p i))


lemma hharray_eq_hhadd [PartialCommMonoid val] :
  hharray s L p =
    (p i ~⟨i in s⟩~> val.val_int L.length) +
    ∑ i in ⟦(0 : ℤ), ↑L.length⟧, (p j + 1 + i.natAbs ~⟨j in s⟩~> L[i]!) := by
  srw hharray harray
  srw bighstar_eq; rotate_right
  { move=> a ?; srw -hadd_disjoint_hstar
    srw hseg_eq_bighstar //; apply hProp.disjoint_sum=> /== i ??
    apply single_disjoint; move: (p a); unfold loc; omega }
  srw -bighstar_hhadd [2]bighstar_eq; rotate_right
  { move=> a ?;
    rewrite [hseg_eq_bighstar]
    { srw -sum_disjoint_hstar=> /== *
      apply single_disjoint
      move: (p a); unfold loc; omega }
    sdone }
  srw -bighstar_sum //

def hharray_int (L :List Int) (p : α -> loc) : hhProp :=
  hharray s (L.map val.val_int) p

lemma hharray_int_eq_hhadd [PartialCommMonoid val] :
  hharray_int s L p =
    (p i ~⟨i in s⟩~> val.val_int L.length) +
    ∑ i in ⟦(0 : ℤ), ↑L.length⟧, (p j + 1 + i.natAbs ~⟨j in s⟩~> val.val_int L[i]!) := by
  srw hharray_int hharray_eq_hhadd /==; congr! 4
  rename_i i iin _; simp at iin
  srw ?getElem!_pos // <;> try omega
  erw [List.getElem_map]=> //==; omega

-- lemma getElem_mapIdx (L : List α)
--   (_ : i < L.length)
--   (_ : i < (L.mapIdx f).length) :
--   (L.mapIdx f)[i] = f i (L[i]) := by admit

-- open AddPCM in
-- lemma hharray_int_hhadd_sum (l : ℤ) (v : Int -> Int) :
--   0 <= l ->
--   l <= L.length ->
--   hharray_int s L p +
--     ∑ i in ⟦0, l⟧, (p j + 1 + i.natAbs ~⟨j in s⟩~> v i) =
--     hharray_int s (L.mapIdx fun i x => if i < l then v i + x else x) p := by
--   move=> ??; srw ?hharray_int_eq_hhadd /== add_assoc; congr
--   srw -(Finset.Ico_union_Ico_eq_Ico (b := l)) //; rotate_left
--   srw ?Finset.sum_union
--   { srw add_assoc [2]add_comm -add_assoc -Finset.sum_add_distrib
--     srw (Finset.sum_congr rfl); rotate_left
--     { move=> ??; srw hhadd_hhsingle }
--     congr 1 <;> apply Finset.sum_congr=> // i /== ?? <;> congr! 3
--     { srw ?getElem!_pos <;> try (move=> /==; omega)
--       erw [getElem_mapIdx] <;> try (move=> /==; omega)
--       srw -?getElem!_pos if_pos <;> try (move=> /==; omega)
--       { srw add_comm; congr! => //; omega }
--       omega }
--     srw ?getElem!_pos <;> try (move=> /==; omega)
--     erw [getElem_mapIdx] <;> try (move=> /==; omega)
--     srw -?getElem!_pos if_neg //; try (move=> /==; omega)
--     omega }
--   { srw Finset.disjoint_left=> /==; omega }
--   srw Finset.disjoint_left=> /==; omega

set_option maxHeartbeats 1600000 in
open EmptyPCM in
lemma harray_int_chip_off (i : ℤ) :
  0 <= i -> i < L.length ->
  ∃ H, hharray_int s L p = (p j + 1 + i.natAbs ~⟨j in s⟩~> val.val_int L[i]!) ∗ H := by
  move=> ??; econstructor
  srw hharray_int_eq_hhadd hhaddE
  srw -(Finset.sdiff_union_of_subset (α := ℤ) (s₁ := {i}) (s₂ := ⟦0, ↑L.length⟧)) //
  srw Finset.sum_union //==; ysimp; ysimp

end
