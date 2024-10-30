import Mathlib.MeasureTheory.Integral.Bochner

import Mathlib.Data.Int.Interval

import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.HyperCommon

open Unary prim val trm
open Classical

notation "⋆" => (Set.univ)

@[app_unexpander Set.univ]
def  unexpandUniv : Lean.PrettyPrinter.Unexpander
  | `($_) => `(⋆)

def val.toReal : val -> ℝ
  | val_real v => v
  | _ => panic! "toInt"

@[simp]
lemma toReal_eq (i : ℝ) : val.toReal i = i := by rfl


@[app_unexpander val.toReal] def unexpandToInt : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `($v)
  | _ => throw ( )

attribute [-simp] fun_insert Bool.forall_bool
attribute [simp] Set.univ_inter

lang_def Lang.get :=
  fun xind xval i z n =>
    let ind := Lang.searchIdx xind i z n in
    xval[ind]

lang_def Lang.int :=
  fun xind xval z n =>
    ref ans := ⟨0 : ℝ⟩ in
    for i in [z:n] {
      let v := xval[i] in
      let ind := xind[i] in
      let i' := i + 1 in
      let ind' := xind[i'] in
      let ln := ind' - ind in
      let v := v * ln in
      ans += v
    }; !ans

variable (xind xval : loc) (z n : ℤ) (N : ℕ)
variable (x_ind : ℤ -> ℝ) (x_val : ℤ -> ℝ)

#hint_yapp triple_hharrayFun_get
#hint_yapp triple_hharrayFun_length
#hint_yapp htriple_eq
#hint_yapp htriple_get
#hint_yapp htriple_subr
#hint_yapp htriple_mulr
#hint_yapp htriple_le
#hint_yapp htriple_lt
#hint_yapp htriple_add

section Unary

variable (x_ind_montone : MonotoneOn x_ind ⟦z, n+1⟧)
variable (zLn : z < n) (oLz : 0 <= z) (nLN : n < N)
include x_ind_montone zLn oLz nLN

lemma get_spec_in (l : ℕ) (k : ℤ) (s : Set ℝ) :
  k ∈ ⟦z, n⟧ ->
  s ⊆ Set.Ico (x_ind k) (x_ind (k + 1)) ->
  arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) ==>
    WP [l| i in s => Lang.get xind xval ⟨i.val⟩ z ⟨n+1⟩] { v,
     ⌜ v = fun _ => val_real $ x_val k ⌝ ∗
     arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
     arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) } := by
  move=> /== ???
  let lem := @Lang.searchIdx_hspec k
  ywp; yapp lem => /== //
  yapp; ysimp


attribute [-simp] Finset.mem_Ico
omit oLz nLN in
lemma x_ind_union :
  Set.Ico (x_ind z) (x_ind n) = ⋃ i ∈ Finset.Ico z n, Set.Ico (x_ind i) (x_ind (i + 1)) := by
  srw iUnion_eq_sum'
  move: x_ind_montone (zLn)
  apply Int.le_induction (m := z) (n := n)=> //' /== n ? ih mon ?
  srw -(Set.Ico_union_Ico_eq_Ico (b := x_ind n))
  { scase: [z = n]=> [?|->]
    { srw ?ih //'
      { srw [2]sum_Ico_predr //== }
      move=> ? /== *; apply mon=> /== //' }
    srw Set.Ico_eq_empty_of_le //' /==
    shave->: Finset.Ico n (n + 1) = Singleton.singleton n
    { move=> ! /==; simp [Finset.mem_Ico ]=> //' }
    srw Finset.sum_singleton }
  all_goals apply mon=> /== //'

open MeasureTheory

set_option maxRecDepth 1500 in
set_option maxHeartbeats 1600000 in
lemma intergal_spec (r : ℝ)  :
  { arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.int xind xval z n]
  [2| i in Set.Ico (x_ind z) (x_ind n) => Lang.get xind xval ⟨i.val⟩ z ⟨n+1⟩]
  {v,
    ⌜v ⟨1,r⟩ = ∫ i in Set.Ico (x_ind z) (x_ind n), (v ⟨2,i⟩).toReal⌝ ∗
    arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) } := by
  yin 1: ywp; yref ans;
  srw x_ind_union //' (foo''' 2) ?(foo''' 0)
  let op := fun (hv : hval ℝˡ) i => ∫ j in Set.Ico (x_ind i) (x_ind (i + 1)), (hv ⟨2,j⟩).toReal
  let P := fun (hv : hval ℝˡ) i => IntegrableOn (fun j => (hv ⟨2,j⟩).toReal) (Set.Ico (x_ind i) (x_ind (i + 1)))
  yfor+. with
    (Q := fun i hv => ans ~⟨k in ⟪1, {r}⟫⟩~> op hv i ∗ ⌜P hv i⌝)
    (H₀ := ans ~⟨i in ⟪1, {r}⟫⟩~> val_real 0) <;> try simp [op, P]
  { move=> j > /== ?? eq; congr! 2
    { congr! 2; apply MeasureTheory.setIntegral_congr
      { exact measurableSet_Ico }
      move=> ?? /=; srw eq // }
    apply MeasureTheory.integrableOn_congr_fun
    { move=> ?? /=; srw eq // }
    exact measurableSet_Ico }
  { move=> > ??;
    yin 1: sdo 6 ystep=> //'; yapp
    yapp get_spec_in=> //';
    { ysimp=> //' ? _
      congr; srw MeasureTheory.setIntegral_const
      srw Real.volume_Ico mul_comm ENNReal.toReal_ofReal /==
      apply x_ind_montone=> /== //' }
    simp [Finset.mem_Ico ]=> //' }
  yapp=> ?; ysimp=> /==
  srw MeasureTheory.integral_finset_biUnion //'
  simp=> i /== ?? j ?? ?
  scase: [i < j]=> ?
  { left; right; apply x_ind_montone=> /== //' }
  right; left; apply x_ind_montone=> /== //'

end Unary
