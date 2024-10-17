import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.HyperCommon

open Unary prim val trm
open Classical

notation "⋆" => (Set.univ)

@[app_unexpander Set.univ]
def  unexpandUniv : Lean.PrettyPrinter.Unexpander
  | `($_) => `(⋆)

def val.toBool : val -> Bool
  | val_bool v => v
  | _ => panic! "toBool"


@[simp]
noncomputable def propToVal : Prop -> val := fun p => val_bool (decide p)

lemma val_bool_eq_propToVal :
  val_bool b = propToVal p ↔ b = p := by
  simp

noncomputable instance : Coe Prop val := ⟨propToVal⟩

@[simp]
lemma toBool_eq (b : Bool) : val.toBool b = b := by rfl

instance : Coe val Prop := ⟨fun v => v.toBool⟩

@[app_unexpander val.toBool] def unexpandToProp : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `($v)
  | _ => throw ( )

attribute [-simp] fun_insert Bool.forall_bool
attribute [simp] Set.univ_inter
#hint_yapp htriple_ref

instance [Inhabited α] : Inhabited (Labeled α) := ⟨⟨0, default⟩⟩

@[heapSimp]
lemma bighstar_hhempty' (s : Set α) :
   [∗ in s | hempty] = emp :=
  by sby unfold hhempty bighstar bighstarDef hEmpty=> /= !?; simp[hempty]=> ⟨?!|->⟩

theorem biUnion_prod_const (s': Set ι) {s : ι → Set α} {t : Set β} :
  (⋃ i ∈ s', s i) ×ˢ t = ⋃ i ∈ s', s i ×ˢ t := by
  ext
  simp=> ⟨|⟩ ![] // ![] //

lang_def Lang.get :=
  fun xind xval i z n =>
    let ind := Lang.findIdx xind i z n in
    let outOfBounds := (ind = n) in
    if outOfBounds then false
    else xval[ind]

lang_def Lang.nonempty :=
  fun xind xval z n =>
    ref ans := false in
    for i in [z:n] {
      let v := xval[i] in
      ans ||= v
    };
    let r := !ans in
    free ans; r

lang_def Lang.get2 :=
  fun xind xval xidx i j =>
    let M' := len xidx in
    let M := M' - 1 in
    let oLi := 0 <= i in
    let iLM := i < M in
    let inBounds := oLi && iLM in
    if inBounds then
      let ind := xidx[i] in
      let i' := i + 1 in
      let ind' := xidx[i'] in
      Lang.get xind xval j ind ind'
    else false

lang_def Lang.nonempty2 :=
  fun xind xval xidx =>
    let M' := len xidx in
    let M := M' - 1 in
    let ans := ref false in
    for i in [0:M] {
      let ind := xidx[i] in
      let i' := i+1 in
      let ind' := xidx[i'] in
      let ans' := Lang.nonempty xind xval ind ind' in
      ans ||= ans'
    };
    let r := !ans in
    free ans; r

variable (xind xval : loc) (z n : ℤ) (N : ℕ)
variable (x_ind : ℤ -> ℝ) (x_val : ℤ -> Bool)

#hint_yapp triple_hharrayFun_get
#hint_yapp triple_hharrayFun_length
#hint_yapp htriple_eq
#hint_yapp htriple_get
#hint_yapp htriple_free
#hint_yapp htriple_sub
#hint_yapp htriple_le
#hint_yapp htriple_lt
#hint_yapp htriple_add

section Unary

variable (x_ind_uniq : Set.InjOn x_ind ⟦z, n⟧)
variable (zLn : z <= n) (oLz : 0 <= z) (nLN : n <= N)
include x_ind_uniq zLn oLz nLN



lemma get_spec_out (l : ℕ) (s : Set ℝ) :
  (∀ i ∈ s, i ∉ x_ind '' ⟦z, n⟧) ->
  arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ==>
    WP [l| i in s => Lang.get xind xval ⟨i.val⟩ z n] { v,
     ⌜ v = fun _ => val_bool false ⌝ ∗
     arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) } := by
  move=> ?
  ywp; yapp Lang.findIdx_hspec_out
  ywp; yapp
  ywp; yif=> // _; ywp; yval; ysimp

notation "·" => (Set.univ)

def toProp : val -> Prop
  | val_bool v => v
  | _ => False

instance : Coe val Prop := ⟨toProp⟩

-- @[app_unexpander toProp] def unexpandToProp : Lean.PrettyPrinter.Unexpander
--   | `($_ $v) => `($v)
--   | _ => throw ( )

attribute [-simp] fun_insert hhwandE
lemma get_spec_in (l : ℕ) (k : ℤ) :
  z <= k ∧ k < n ->
  arr⟨⟪l,{x_ind k}⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,{x_ind k}⟫⟩(xval, x in N => x_val x) ==>
    WP [l| i in {x_ind k} => Lang.get xind xval ⟨i.val⟩ z n] { v,
     ⌜ v = fun _ => val_bool $ x_val k ⌝ ∗
     arr⟨⟪l,{x_ind k}⟫⟩(xind, x in N => x_ind x) ∗
     arr⟨⟪l,{x_ind k}⟫⟩(xval, x in N => x_val x) } := by
  move=> ?
  ywp; yapp Lang.findIdx_hspec
  { ywp; yapp
    ywp; yifF
    { move=> ? /== _ ->; srw Function.invFunOn_app_eq // }
    srw hwp_labSet_single; yapp
    { ysimp; funext i; srw Function.invFunOn_app_eq // }
    move=> ? _; srw Function.invFunOn_app_eq // }
  move=> [] ?/== _; exists k


set_option maxHeartbeats 1600000 in
lemma nonempty_spec (r : ℝ)  :
  { arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.nonempty xind xval z n]
  [2| i in Set.univ => Lang.get xind xval ⟨i.val⟩ z n]
  {v,
    ⌜ v ⟨1,r⟩ = ∃ i : ℝ, v ⟨2,i⟩ ⌝ ∗
    arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) } := by
  yfocus 2, x_ind '' ⟦z, n⟧
  yapp get_spec_out=> /==;
  simp [fun_insert]
  yin 1: ywp; yref=> p
  srw [1]Set.image_eq_iUnion
  yfor|| with
    (Q := fun i hv => p j ~⟨j in ⟪1, {r}⟫⟩~> (hv ⟨2,x_ind i⟩).toBool)
    (H₀ := p i ~⟨i in ⟪1, {r}⟫⟩~> false)
  { move=> >*
    yin 1: ystep; yapp
    yapp get_spec_in; ysimp }
  { sdone }
  ystep; ystep; ywp; yval
  ysimp=> /== ⟨|⟩ /==
  { move=> i *; exists (x_ind i); srw if_pos //==; exists i }
  move=> i; scase_if=> /== i ?? <- ?; exists i

end Unary

variable (xidx : loc) (x_idx : ℤ -> ℤ) (M : ℕ)
variable (x_idx_monotonne : MonotoneOn x_idx ⟦0, M+1⟧)
variable (x_idx_M : x_idx M = N) (x_idx_0 : x_idx 0 = 0)
variable (x_ind_uniq : ∀ i ∈ ⟦0, M⟧, Set.InjOn x_ind ⟦x_idx i, x_idx (i + 1)⟧)

set_option maxHeartbeats 1600000 in
lemma get2_spec_out (l : ℕ) (s : Set (ℤ × ℝ)) :
  (∀ ij ∈ s, ij.1 ∉ ⟦0,M⟧) ->
  arr⟨⟪l,s⟫⟩(xidx, x in M+1 => x_idx x) ==>
    WP [l| ij in s => Lang.get2 xind xval xidx ⟨ij.val.1⟩ ⟨ij.val.2⟩] { v,
     ⌜ v = fun _ => val_bool false ⌝ ∗
     arr⟨⟪l,s⟫⟩(xidx, x in M+1 => x_idx x) } := by
  move=> out;
  sdo 5 ystep
  ywp; yifF
  { simp [One.one]; scase=> l [z r] /== _ /out /== }
  ywp; yval; ysimp

include x_idx_monotonne x_idx_M x_idx_0 x_ind_uniq

open Classical

attribute [-simp] Set.singleton_prod


set_option maxRecDepth 1500
set_option maxHeartbeats 4000000
lemma nonempty2_spec (z : ℤ) (r : ℝ)  :
  { arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) ∗
    arr⟨⋆⟩(xidx, x in M+1 => x_idx x) }
  [1| x in {(z,r)} => Lang.nonempty2 xind xval xidx]
  [2| ij in ⋆ => Lang.get2 xind xval xidx ⟨ij.val.1⟩ ⟨ij.val.2⟩]
  {v,
    ⌜ v ⟨1,z,r⟩ = ∃ (i : ℤ) (j : ℝ), v ⟨2,i,j⟩ ⌝ ∗ ⊤ } := by
  yfocus 2, ⟦0, M⟧ ×ˢ ⋆
  yapp get2_spec_out=> /==; simp [fun_insert]
  yin 1: (sdo 3 ystep)=> p;
  srw -((Set.Ico (0 : ℤ) M).biUnion_of_singleton)
  srw biUnion_prod_const
  yfor|| with
    (Q := fun i hv => p k ~⟨k in ⟪1, {(z,r)}⟫⟩~> decide (∃ j : ℝ, hv ⟨2,i,j⟩))
    (H₀ := p i ~⟨i in ⟪1, {(z,r)}⟫⟩~> false);
  { move=> j > /== ?? eq; congr! 7; srw eq // }
  { move=> i b ??
    yin 1: (sdo 3 ystep)=> //'; simpWP
    yin 2:
      sdo 5 ystep
      ywp; yifT=> /== //'
      sdo 3 ystep=> /== //'
      simpWP=> /=
    srw hhsingle_singleton /=
    ysubst with (σ := Prod.snd)
    { ysimp }
    { scase; simp }
    zapp nonempty_spec
    { apply x_ind_uniq=> //' }
    { apply x_idx_monotonne=> /== //' }
    { srw -x_idx_0; apply x_idx_monotonne=> /== //' }
    { srw -x_idx_M; apply x_idx_monotonne=> /== //' }
    move=> ->; yapp; ysimp }
  { auto }
  (sdo 2 ystep); ywp; yval; ysimp
  simp=> ⟨|⟩ ![] i
  { move=> ? r eq; exists i, r=> //' }
  move=> r; scase_if=> /== ?? eq;
  exists i=> ⟨//'|⟩; exists r=> //';
