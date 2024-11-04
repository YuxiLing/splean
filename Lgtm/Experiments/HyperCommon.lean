import Lgtm.Hyper.ProofMode
import Lgtm.Hyper.ArraysFun

import Lgtm.Experiments.UnaryCommon


open Unary prim val trm

namespace Lang
notation "arr⟨"s"⟩(" p "," x " in " n " => " f ")" => hharrayFun s (fun x => f) n (fun _ => p)

lemma findIdx_hspec (l : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  (∀ i ∈ ⟪l,s⟫, target i ∈ f '' ⟦z, n⟧) ->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| findIdx arr ⟨target i⟩ z n])
    fun v ↦ ⌜v = fun i ↦ val_int (f.invFunOn ⟦z, n⟧ (target i))⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec; xsimp=> //

@[yapp]
lemma findIdx_hspec' (l : ℕ) (f : ℤ -> ℝ) (s : Set α) (i : ℤ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪l, s⟫ (fun _ ↦ [lang| findIdx arr ⟨f i⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  sorry

lemma findIdx_hspec_out (l : ℕ) (f : ℤ -> ℝ) (target : Labeled α -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  (∀ i ∈ ⟪l,s⟫, target i ∉ f '' ⟦z, n⟧) ->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
     hwp ⟪l, s⟫ (fun i ↦ [lang| findIdx arr ⟨target i⟩ z n]) fun v ↦ ⌜v = fun _ ↦ val_int $ n⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ??
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp findIdx_spec_out

lemma find2Idx_hspec  (l : ℕ) (f₁ f₂ : ℤ -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn (fun i => (f₁ i, f₂ i)) ⟦z, n⟧ ->
  k ∈ Finset.Ico z n ->
  arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) ==>
    hwp ⟪l, s⟫ (fun _ ↦ [lang| find2Idx arr₁ arr₂ ⟨f₁ k⟩ ⟨f₂ k⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int k⌝ ∗ arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) := by
  move=> ??
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp find2Idx_spec

lemma find2Idx_hspec_out  (l : ℕ) (f₁ f₂ : ℤ -> ℝ) (s : Set α) (tgt₁ tgt₂ : αˡ -> ℝ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn (fun i => (f₁ i, f₂ i)) ⟦z, n⟧ ->
  (∀ᵉ (i ∈ ⟪l,s⟫) (j ∈ ⟦z,n⟧), ¬ (f₁ j = tgt₁ i ∧ f₂ j = tgt₂ i)) ->
  arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| find2Idx arr₁ arr₂ ⟨tgt₁ i⟩ ⟨tgt₂ i⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int n⌝ ∗ arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) := by
  move=> ??
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp find2Idx_spec_out


lemma find2Idx_hspec'  (l : ℕ) (f₁ : ℤ -> ℝ) (f₂ : ℤ -> ℤ) (s : Set α)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn (fun i => (f₁ i, f₂ i)) ⟦z, n⟧ ->
  k ∈ Finset.Ico z n ->
  arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) ==>
    hwp ⟪l, s⟫ (fun _ ↦ [lang| find2Idx arr₁ arr₂ ⟨f₁ k⟩ ⟨f₂ k⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int k⌝ ∗ arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) := by
  move=> ??
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp find2Idx_specZ'

lemma find2Idx_hspec_out'  (l : ℕ) (f₁ : ℤ -> ℝ) (f₂ : ℤ -> ℤ) (s : Set α) (tgt₁ : αˡ -> ℝ) (tgt₂ : αˡ -> ℤ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn (fun i => (f₁ i, f₂ i)) ⟦z, n⟧ ->
  (∀ᵉ (i ∈ ⟪l,s⟫) (j ∈ ⟦z,n⟧), ¬ (f₁ j = tgt₁ i ∧ f₂ j = tgt₂ i)) ->
  arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| find2Idx arr₁ arr₂ ⟨tgt₁ i⟩ ⟨tgt₂ i⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int n⌝ ∗ arr⟨⟪l,s⟫⟩(arr₁, x in N => f₁ x) ∗ arr⟨⟪l,s⟫⟩(arr₂, x in N => f₂ x) := by
  move=> ??
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? i ??
  xapp find2Idx_spec_outZ


@[yapp]
lemma or_eq_hspec (a b : α -> Bool) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app val_or_eq (p i) (b i)) (fun _ => p i ~⟨i in s⟩~> (b i || a i)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (b i || a i))=> ??; apply or_eq_spec

@[yapp]
lemma incr_hspec (a : α -> ℤ) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app incr (p i)) (fun _ => p i ~⟨i in s⟩~> (a i + 1)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (a i + 1))=> ??; apply incr_spec

@[yapp]
lemma add_eq_hspec (a b : α -> ℝ) (p : α -> loc) :
  (p i ~⟨i in s⟩~> a i) ==>
    hwp s (fun i => trm_app val_add_eq (p i) (b i)) (fun _ => p i ~⟨i in s⟩~> (b i + a i)) := by
  apply htriple_prod (Q := fun i _ => p i ~~> (b i + a i))=> ??; apply add_eq_spec

@[yapp]
lemma and_hspec (a b : α -> Bool) :
  emp ==>
    hwp s (fun i => trm_app val_and (a i) (b i)) (fun v => ⌜v = fun i => val_bool (a i && b i)⌝) := by
  apply htriple_prod_val_eq_emp => ??; apply and_spec

lemma searchIdx_hspec (l : ℕ) (f : ℤ -> ℝ) (s : Set ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n < N) :
  MonotoneOn f ⟦z, n+1⟧ ->
  i ∈ ⟦z, n⟧ ->
  (s ⊆ Set.Ico (f i) (f (i+1)))->
  arr⟨⟪l,s⟫⟩(arr, x in N => f x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchIdx arr ⟨i.val⟩ z ⟨n+1⟩])
    fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l, s⟫⟩(arr, x in N => f x) := by
  move=> ???
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchIdx_spec'

lemma searchSRLE_hspec (f : α -> ℝ) (l : ℕ) (lf rf : ℤ -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  (∀ i ∈ ⟦z, n⟧, lf i <= rf i) ->
  (∀ i ∈ ⟦z, n-1⟧, rf i <= lf (i + 1)) ->
  i ∈ ⟦z, n⟧ ->
  (f '' s ⊆ Set.Ico (lf i) (rf i))->
  arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE left right ⟨f i.val⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int i⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) := by
  move=> ??? sub
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchSparseRLE_spec'=> //
  move: (@sub (f j)); sapply=> //

lemma searchSRLE_hspec_out (f : α -> ℝ) (l : ℕ) (lf rf : ℤ -> ℝ) (s : Set α)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  (∀ i ∈ ⟦z, n⟧, lf i <= rf i) ->
  (∀ i ∈ ⟦z, n-1⟧, rf i <= lf (i + 1)) ->
  Disjoint (f '' s) (⋃ i ∈ ⟦z, n⟧, Set.Ico (lf i) (rf i)) ->
  arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) ==>
    hwp ⟪l, s⟫ (fun i ↦ [lang| searchSRLE left right ⟨f i.val⟩ z n])
    fun v ↦ ⌜v = fun _ ↦ val_int n⌝ ∗ arr⟨⟪l,s⟫⟩(left, x in N => lf x) ∗ arr⟨⟪l,s⟫⟩(right, x in N => rf x) := by
  move=> ?? /Set.disjoint_left ?
  srw ?hharrayFun bighstar_hhstar
  apply htriple_prod_val_eq=> [] /== ? j ??
  xapp searchSparseRLE_spec_out


end Lang
