import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.HyperCommon

open Unary prim val trm

lang_def Lang.get :=
  fun xind xval i =>
    let N := len xind in
    let ind := Lang.findIdx xind i in
    let outOfBounds := (ind = N) in
    if outOfBounds then false
    else xval[ind]

lang_def Lang.nonempty :=
  fun xind xval =>
    let N := len xind in
    ref ans := false in
    for i in [0:N] {
      let v := xval[i] in
      ans ||= v
    }
    let a := !ans in
    a

variable (xind xval : loc) (N : ℕ)
variable (x_ind : ℤ -> ℝ) (x_val : ℤ -> Bool)
variable (x_ind_uniq : Set.InjOn x_ind ⟦0, (N : ℤ)⟧)
include x_ind_uniq

#hint_yapp triple_hharrayFun_get
#hint_yapp triple_hharrayFun_length
#hint_yapp htriple_eq

lemma get_spec_out (s : Set ℝ) :
  (∀ i ∈ s, i ∉ x_ind '' ⟦0, (N : ℤ)⟧) ->
  arr⟨⟪n,s⟫⟩(xind, x in N => x_ind x) ==>
    WP [n| i in s => Lang.get xind xval ⟪i.val⟫] { v,
     ⌜ v = fun _ => val_bool false ⌝ ∗
     arr⟨⟪n,s⟫⟩(xind, x in N => x_ind x) } := by
  move=> ?
  ywp; yapp
  ywp; yapp Lang.findIdx_hspec_out
  ywp; yapp
  ywp; yif=> // _; ywp; yval; ysimp

notation "·" => (Set.univ)

def toProp : val -> Prop
  | val_bool v => v
  | _ => False

instance : Coe val Prop := ⟨toProp⟩

@[app_unexpander toProp] def unexpandToProp : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `($v)
  | _ => throw ( )

attribute [-simp] fun_insert hhwandE


lemma nonempty_spec (r : ℝ)  :
  { arr⟨·⟩(xind, x in N => x_ind x) ∗
    arr⟨·⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.nonempty xind xval]
  [2| i in · => Lang.get xind xval ⟪i.val⟫]
  {v,
    ⌜ v ⟨1,r⟩ = ∃ i : ℝ, v ⟨2,i⟩ ⌝ ∗ (⊤ : hhProp (Labeled ℝ)) } := by
  srw LGTM.triple
  yfocus 1
  ywp ; yapp
  ywp; yref p


  -- yfocus 2, (x_ind '' ⟦0, (N : ℤ)⟧)
  -- yapp get_spec_out
  -- ysimp_start
  -- ysimp_step
  -- ysimp_step
  -- ysimp_step
  -- ysimp_step
  -- ysimp_step
  -- ysimp_step
  -- ysimp_step
  sorry


  -- yfocus 2, (x_ind '' ⟦0, (N : ℤ)⟧)
