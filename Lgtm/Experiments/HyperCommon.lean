import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.UnaryCommon


open Unary prim val trm

namespace Lang
notation "arr⟨"s"⟩(" p "," x " in " n " => " f ")" => hharrayFun s (fun x => f) n (fun _ => p)

lemma findIdx_hspec (n : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α) (N : ℕ) :
  Set.InjOn f ⟦0, (N : ℤ)⟧ ->
  (∀ i ∈ ⟪n,s⟫, target i ∈ f '' ⟦0, (N : ℤ)⟧) ->
  arr⟨⟪n,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪n, s⟫ (fun i ↦ [lang| findIdx arr ⟪target i⟫])
    fun v ↦ ⌜v = fun i ↦ val_int (f.invFunOn ⟦0, (N : ℤ)⟧ (target i))⌝ ∗ arr⟨⟪n, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec; xsimp=> //

lemma findIdx_hspec_out (n : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α) (N : ℕ) :
  Set.InjOn f ⟦0, (N : ℤ)⟧ ->
  (∀ i ∈ ⟪n,s⟫, target i ∉ f '' ⟦0, (N : ℤ)⟧) ->
  arr⟨⟪n,s⟫⟩(arr, x in N => f x) ==>
     hwp ⟪n, s⟫ (fun i ↦ [lang| findIdx arr ⟪target i⟫]) fun v ↦ ⌜v = fun _ ↦ val_int $ N⌝ ∗ arr⟨⟪n, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec_out

@[yapp]
lemma or_eq_hspec (a b : α -> Bool) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app val_or_eq (p i) (b i)) (fun _ => p i ~⟨i in s⟩~> (a i || b i)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (a i || b i))=> ??; apply or_eq_spec


end Lang
