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

lang_def Lang.get2 :=
  fun xleft xright yprt yleft yright yval i j M =>
    let ind := Lang.searchSRLE yleft yright i z n in
    let outOfBounds := (ind = M) in
    if outOfBounds then ⟨0:ℝ⟩
    else
      let yz := yprt[ind] in
      let ind' := ind + 1 in
      let yn := yprt[ind'] in
      Lang.get yleft yright yval j yz yn in

lang_def Lang.get :=
  fun xleft xright xval i z n =>
    let ind := Lang.searchSRLE xleft xright i z n in
    let outOfBounds := (ind = n) in
    if outOfBounds then ⟨0:ℝ⟩
    else xval[ind]

lang_def Lang.linearInterp :=
  fun xleft xright xval z n =>
    ref ans := ⟨0 : ℝ⟩ in
    for i in [z:n] {
      let v    := xval[i] in
      let indl  := xleft[i] in
      let indr := xright[i] in
      let ln   := indr - indl in
      let v    := v * ln in
      ans += v
    }; !ans

lang_def Lang.bilinearInterp :=
  fun xleft xright yprt yleft yright yval N =>
    ref ans := ⟨0 : ℝ⟩ in
    let N' := N - 1 in
    for i in [0:N'] {
      let indl := xleft[i] in
      let indr := xright[i] in
      let ln   := indr - indl in
      let yz  := yprt[i] in
      let i' := i + 1 in
      let yn  := yprt[i'] in
      let ans' := Lang.linearInterp yleft yright yval yz yn in
      let ans' := ans' * ln in
      ans += ans'
    }; !ans

variable (xleft xright xval : loc) (z n : ℤ) (N : ℕ)
variable (x_left x_right : ℤ -> ℝ) (x_val : ℤ -> ℝ)

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

variable (x_lr : ∀ i ∈ ⟦z, n⟧, x_left i <= x_right i)
variable (x_rl : ∀ i ∈ ⟦z, n-1⟧, x_right i <= x_left (i + 1))
variable (zLn : z < n) (oLz : 0 <= z) (nLN : n <= N)
include x_lr x_rl zLn oLz nLN

lemma get_spec_in (l : ℕ) (k : ℤ) (s : Set ℝ) :
  k ∈ ⟦z, n⟧ ->
  s ⊆ Set.Ico (x_left k) (x_right k) ->
  arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
  arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
  arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) ==>
    WP [l| i in s => Lang.get xleft xright xval ⟨i.val⟩ z n] { v,
    ⌜ v = fun _ => val_real $ x_val k ⌝ ∗
    arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
    arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
    arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) } := by
  move=> /== ???
  let lem := @Lang.searchSRLE_hspec k
  ywp; yapp lem => /== //; clear lem
  ystep; ywp; yifF=> /== //'
  yapp; ysimp=> //'


lemma get_spec_out (l : ℕ) (s : Set ℝ) :
  Disjoint s (⋃ i ∈ ⟦z, n⟧, Set.Ico (x_left i) (x_right i)) ->
  arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
  arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
  arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) ==>
    WP [l| i in s => Lang.get xleft xright xval ⟨i.val⟩ z n] { v,
    ⌜ v = fun _ => val_real 0 ⌝ ∗
    arr⟨⟪l,s⟫⟩(xleft, x in N => x_left x) ∗
    arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ∗
    arr⟨⟪l,s⟫⟩(xval, x in N => x_val x) } := by
  move=> /== ?
  ywp; yapp Lang.searchSRLE_hspec_out => /== //
  ystep; ywp; yifT=> //'
  ywp; yval; ysimp=> //'

open MeasureTheory

attribute [-simp] Finset.mem_Ico

set_option maxRecDepth 1500 in
set_option maxHeartbeats 1600000 in
lemma ilinearInterp_spec (r : ℝ)  :
  { arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.linearInterp xleft xright xval z n]
  [2| i in ⋆   => Lang.get xleft xright xval ⟨i.val⟩ z n]
  {v,
    ⌜v ⟨1,r⟩ = ∫ i, (v ⟨2,i⟩).toReal⌝ ∗
    arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) } := by
  yfocus 2, ⋃ i ∈ ⟦z,n⟧, Set.Ico (x_left i) (x_right i)
  yapp get_spec_out=> //'; rotate_left
  { exact Set.disjoint_sdiff_left }
  simp [fun_insert, OfNat.ofNat, Zero.zero]
  yin 1: ywp; yref ans
  let op := fun (hv : hval ℝˡ) i => ∫ j in Set.Ico (x_left i) (x_right i), (hv ⟨2,j⟩).toReal
  let P := fun (hv : hval ℝˡ) i => IntegrableOn (fun j => (hv ⟨2,j⟩).toReal) (Set.Ico (x_left i) (x_right i))
  yfor+. with
    (Q := fun i hv => ans ~⟨k in ⟪1, {r}⟫⟩~> op hv i ∗ ⌜P hv i⌝)
    (H₀ := ans ~⟨i in ⟪1, {r}⟫⟩~> val_real 0) <;> try simp [op, P]
  { move=> j > /== ?? eq; congr! 2
    { congr! 2; apply setIntegral_congr
      { exact measurableSet_Ico }
      move=> ?? /=; srw eq // }
    apply integrableOn_congr_fun
    { move=> ?? /=; srw eq // }
    exact measurableSet_Ico }
  { move=> > ??;
    yin 1: sdo 5 ystep=> //'; yapp
    yapp get_spec_in=> //';
    { ysimp=> //' ? _
      congr; srw setIntegral_const
      srw Real.volume_Ico mul_comm ENNReal.toReal_ofReal /==
      apply x_lr; simp [Finset.mem_Ico]=> // }
    simp [Finset.mem_Ico ]=> //' }
  yapp=> ?; ysimp=> /==
  srw -integral_finset_biUnion //'
  { srw -[2](setIntegral_eq_integral_of_forall_compl_eq_zero
             (s := ⋃ i ∈ Finset.Ico z n, (Set.Ico (x_left i) (x_right i))))
    { apply setIntegral_congr=> [|?]//
      apply Finset.measurableSet_biUnion=> //' }
    move=> /== ??; srw if_neg // }
  move=> x /== ?? y ?? ?
  scase: [x < y]
  { move=> ?; shave: y < x; omega
    move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
    left; right; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //' }
  move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
  right; left; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //'

end Unary
