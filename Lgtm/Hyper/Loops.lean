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

instance : Zero hhProp where zero := emp

instance : Add hhProp where add s t := s ∗ t

@[simp]
lemma hhProp_add_def (s t : hhProp) : s + t = s ∗ t := rfl

@[simp]
lemma hhProp_zero_def : (0 : hhProp) = emp := rfl

instance : Zero hProp where zero := hempty

instance : Add hProp where add s t := s ∗ t

@[simp]
lemma hProp_add_def (s t : hProp) : s + t = s ∗ t := rfl

@[simp]
lemma hProp_zero_def : 0 = hempty := rfl


instance : AddCommMonoid hhProp where
  nsmul := nsmulRec
  add_assoc := by move=> > /==; srw hhstar_assoc
  zero_add  := by move=> > /==; srw hhstar_hhempty_l
  add_zero  := by intros; simp; apply hhstar_hhempty_r
  add_comm  := by intros; simp; apply hhstar_comm

attribute [-simp] hhProp_add_def

instance : AddCommMonoid hProp where
  nsmul := nsmulRec
  add_assoc := by move=> > /==; srw hstar_assoc
  zero_add  := by move=> > /==; srw hstar_hempty_l
  add_zero  := by intros; simp; apply hstar_hempty_r
  add_comm  := by intros; simp; apply hstar_comm

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
lemma set_plusE (s₁ s₂ : Set α) : s₁ + s₂ = s₁ ∪ s₂ := by rfl
@[simp]
lemma sot_0E  : (0 : Set α) = ∅ := by rfl


macro_rules
  | `(tactic| ssr_triv) => `(tactic| omega)

namespace LGTM

namespace Disjoint

section ForLoop

lemma wp_for_aux
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
  ychange wp_align_step_disj
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
lemma wp_for (Inv : Int -> hval -> hhProp) (sᵢ : Int -> Set α) (ht : htrm) :
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
     ychange (wp_for_aux (sᵢ := sᵢ) (i := z) (z := z) (n := n))=> //
     rotate_right
     { sby apply LGTM.wp_conseq=> ? }
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

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

lemma sum_bighstar (H : β -> α -> hProp) :
  -- Finset.sum fs (bighstar s H)=
  ∑ i in fs, H i ∗↑ s = [∗ a in s| ∑ i in fs, H i a] := by sorry

lemma sum_bighstar_set (H : α -> hProp) (s : β -> Set α) :
  -- Finset.sum fs (bighstar s H)=
  H ∗↑ ∑ i in fs, s i = ∑ i in fs, H ∗↑ s i := by sorry

lemma hhimpl_bighstar_himpl
   (Q R : α -> hProp) (s : Set α) :
  (∀ x ∈ s, himpl (Q x) (R x)) ->
  [∗ i in s| Q i] ==> [∗ i in s| R i] := by
  sorry

lemma choose_fun2 {α α' β : Type} (b₀ : β)  (p : α -> α' -> β -> Prop) (s : Set α) (s' : Set α') :
  (∀ᵉ (a ∈ s) (a' ∈ s'), ∃ b : β, p a a' b) -> (∃ f : α -> α' -> β, (∀ᵉ (a ∈ s) (a' ∈ s'), p a a' (f a a'))) := by
  -- move=> pH
  -- exists (fun a => if h : a ∈ s then choose (pH a h) else b₀)=> /=
  -- move=> a inS
  -- srw dif_pos //; apply choose_spec
  sorry

lemma wp_for_bighop (β : Type) [inst : Inhabited β]
  (z n : Int)
  (Q : Int -> hval -> α -> hProp)
  (R R' : α -> hProp)
  (H₀ : α -> hProp)
  (Qgen : Int -> β -> α -> hProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= n ->
  (∀ j hv₁ hv₂, ∀ a ∈ s', z <= j ∧ j <= n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁ a) = (Q j hv₂ a)) ->
  s = ∑ i in [[z, n]], sᵢ i ->
  (∀ (hv : hval), ∀ j ∈ [[z,n]], ∀ a ∈ s', ∃ v, H₀ a + ∑ i in [[z, j]], Q i hv a = Qgen j v a) ->
  Disjoint s' s ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (∀ j (v : α -> β), z <= j ∧ j < n ->
    [∗ i in s'| Qgen j (v i) i] ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' ∗↑ s' + [∗ i in s'| Qgen j (v i) i] ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗↑ s' ∗ R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩]
         (fun hv => H₀ ∗↑ s' + (∑ j in [[z, n]], Q j hv ∗↑ s') ∗ R' ∗↑ s) := by
  move=> ? eqQ ? gen dj dij' ind *
  eapply wp_for
    (hv₀ := fun _ => default)
    (Inv := fun i hv =>
      H₀ ∗↑ s' ∗
      (∑ j in [[z, i]], Q j hv ∗↑ s') ∗
      ((∑ j in [[z, i]], R' ∗↑ sᵢ j) ∗ (∑ j in [[i, n]], R ∗↑ sᵢ j)))=> //'
  { move=> > ? hveq; ysimp; srw ?sum_bighstar; apply hhimpl_bighstar_himpl=> a ?
    srw (Finset.sum_congr (s₂ := [[z,j]])); rotate_right 2
    { move=> /== k ??; apply eqQ
      { auto }
      { auto }
      move=> ??; apply hveq=> xin
      sapply: (Set.disjoint_left.mp dj xin)
      srw mem_union; exists k=> ⟨|//⟩ /==; omega }
    all_goals auto }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /(choose_fun2 (b₀ := default))/(_ inst)
    scase=> hv' gen
    srw sum_bighstar -hhstar_assoc bighstar_hhstar bighstar_eq; rotate_left 2
    apply gen; srw //' [2]sum_Ico_succl //' hhProp_add_def
    ychange ind=> //'; apply hhimpl_trans; apply wp_frame; apply hwp_conseq=> hv' /=
    srw [2]bighstar_eq; rotate_left 2
    { move=> ??; srw -gen //' }
    srw -bighstar_hhstar -sum_bighstar [5]sum_Ico_predr //' /== ?hhProp_add_def
    ysimp;
    srw [2]sum_Ico_predr //' /== hhProp_add_def hhstar_comm ?sum_bighstar ?bighstar_hhstar
    srw [2]bighstar_eq; apply hhimpl_refl
    move=> ??; congr 1; apply Finset.sum_congr (s₂ := [[z, j]])=>[//| |]
    { move=> /== k ??; apply eqQ=> //' ? f /== ?
      specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
      move: (Set.disjoint_left.mp dij' f)=> //' }
    apply eqQ=> //' }
  { srw Finset.Ico_self /== //'; subst_vars; srw -sum_bighstar_set
    ysimp }
  move=> hv' /=; subst_vars; srw sum_bighstar_set Finset.Ico_self /==; ysimp
  ysimp


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
          (fun hv' => ∃ʰ b, Inv b (j + 1) (hv ∪_(∑ i in [[z, j]], sᵢ i) hv'))) ->
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
    ychange wp_align_step_disj
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
          (fun hv' => ∃ʰ b, Inv b (j + 1) (hv' ∪_(sᵢ j) hv))) ->
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

end Disjoint

namespace ForLoop

def labSet (l : ℤ) (s : Set α) : Set (ℤ × α) := {(l, a) | a ∈ s}

notation (priority := high) "⟪" l ", " s "⟫" => labSet l s

@[simp]
lemma labelSet_inE :
  ((l, a) ∈ ⟪l', s⟫) = (l = l' ∧ a ∈ s) := by
  simp [labSet]=> //

@[simp]
lemma labelSet_inE' :
  (⟪l', s⟫ (l, a)) = (l = l' ∧ a ∈ s) := by
  apply labelSet_inE


private lemma foo (s : Set α) :
  s a = (a ∈ s) := by rfl

variable (z n : ℤ)
variable (sᵢ : ℤ -> Set α)
variable (s' : Set α)
variable (disj : Disjoint s' s)
variable (seq: s = ∑ i in [[z, n]], sᵢ i)
variable (df : α)
variable (dfN : df ∉ s' ∪ s)

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

private noncomputable def π' : ℤ × α -> α :=
  fun (i, a) =>
    if i ∈ [[z,n]] then
      if a ∈ sᵢ i then a
      else df
    else
      if i = n then
        if a ∈ s' then a
        else df
      else df


local notation "π" => π' z n sᵢ s' df

attribute [simp] π' mem_union

@[simp]
abbrev fs := ∑ i in [[z,n]], ⟪i, sᵢ i⟫

local notation "fs" => fs z n sᵢ

private lemma disj' :
  ∀ i a, a ∈ s' -> a ∈ sᵢ i -> z <= i ∧ i < n -> False := by
  move=> i *
  srw seq -disjoint_union at disj
  specialize disj i ?_=> //'
  move: (Set.disjoint_left.mp disj)=> //

local notation "disj'" => disj' s z n sᵢ s' disj seq

set_option maxHeartbeats 1600000 in
@[simp]
private lemma validSubst_s' :
  validSubst π (⟪n,s'⟫ ∪ fs) ⟪n, s'⟫ := by
  move: (disj')=> d
  simp=> []/== > [/== -> ? | > /== > ?? -> ? > [/== -> ? | /== ? ?? -> ? ] ]
  { move=> > /== [/== -> ?| /== ? ?? -> ? ]
    { srw if_pos //' }
    srw if_pos //' if_pos //' if_pos //' => -> ⟨|⟩ //' *
    exfalso; apply d=> //' }
  { srw if_pos //' if_pos //' if_neg //' if_pos //' if_pos //' => ?
    subst_vars=> ⟨|⟩ //' /== ?; exfalso; apply d=> //' }
  srw if_pos //'


@[simp]
private lemma validSubst_s :
  validSubst π (⟪n,s'⟫ ∪ fs) fs := by
  move: (disj')=> d
  simp=> []/== > [/== -> ? | > /== > ?? -> ? > [/== -> ? | /== y ?? -> ? ] ]
  { move=> > /== [/== -> ?| /== ? ?? -> ? ]
    { srw if_pos //' }
    srw if_pos //' if_pos //' if_pos //' => ? ⟨|⟩ //'; subst_vars
    { srw (@foo (ℤ×α) (n, b) (∑ i ∈ [[z, n]], ⟪i, sᵢ i⟫)) /== //' }
    srw (@foo (ℤ×α) (_, b) (∑ i ∈ [[z, n]], ⟪i, sᵢ i⟫)) /== => *
    subst_vars; exfalso; apply d=> //' }
  { srw if_pos //' if_pos //' if_neg //' if_pos //' if_pos //' => ?
    subst_vars=> ⟨|⟩ //' /== f; exfalso; apply d=> //'
    move: f; srw (@foo (ℤ×α) (n, b) (∑ i ∈ [[z, n]], ⟪i, sᵢ i⟫)) /== //' }
  srw if_pos //' if_pos //' if_pos //' if_pos //'=> ?; subst_vars
  srw ?(@foo (ℤ×α) _ (∑ i ∈ [[z, n]], ⟪i, sᵢ i⟫)) /== => ⟨|⟩ /== *
  exists y; exists x

private lemma ssubst_s' :
  ssubst π (⟪n, s'⟫ ∪ fs) ⟪n, s'⟫ = s' := by
  move=>!x; srw fsubst_inE; rotate_right
  { apply validSubst_s'=> // }
  simp=> ⟨|⟩ /==
  { move=> > [] // }
  move=> ?; exists n, x=> //

private lemma ssubst_s :
  ssubst π (⟪n, s'⟫ ∪ fs) fs = s := by
  move=>!x; srw fsubst_inE; rotate_right
  { apply validSubst_s=> // }
  simp=> ⟨|⟩ /==
  { move=> > [] //== > ?????????
    srw if_pos //' if_pos //'=> ?; subst_vars=> /== ⟨|//⟩ }
  srw seq=> /== i ???; exists i, x=> // ⟨⟨|⟩|⟩
  { right; exists i }
  { exists i }
  srw if_pos=> //


private lemma lem0 : (df ∉ s') ∧ (∀ i, z <= i -> i < n -> df ∉ sᵢ i) := by
  move: seq dfN=> -> /==


set_option maxHeartbeats 1600000 in
private lemma lem1 :
  (∀ a ∈ fs, ∀ a' ∉ fs, π a ≠ π a') := by
  move: (lem0 s z n sᵢ s' seq df dfN)=> [? ?]
  move: (disj') => d
  move=> [] > /== ? ?? -> ? > ?
  srw if_pos //' if_pos //'; scase_if=> /==
  { move=> ??; srw if_neg //' => ? // }
  move=> ?; scase_if=> [?|]
  { scase_if=> ?? //; subst_vars; apply d=> //' }
  move=> ?? //

set_option maxHeartbeats 1600000 in
private lemma lem2 :
  (∀ a ∈ ⟪n,s'⟫, ∀ a' ∉ ⟪n,s'⟫, π a ≠ π a') := by
  move: (lem0 s z n sᵢ s' seq df dfN)=> [? ?]
  move: (disj') => d
  scase=> > /== -> ? > ?; srw if_neg //' if_pos //' if_pos //'
  scase_if=> [/==??|?]
  { scase_if=> ??; apply d=> // }
  scase_if=> [|?? //] ?; srw if_neg //' => ? //

set_option maxHeartbeats 1600000 in
private lemma lem3 :
  (∀ a ∈ ⟪n,s'⟫, ∀ a' ∈ fs, π a ≠ π a') := by
  move=> ? /lem2 /[swap] a /(_ a) /[swap]?; sapply=> //'
  scase: a=> > /[swap] _ /== //

set_option maxHeartbeats 1600000 in
private lemma lem4 :
  (∀ a ∈ ⟪n,s'⟫ ∪ fs, ∀ a' ∉ ⟪n,s'⟫ ∪ fs, π a ≠ π a') := by
  move=> a /[swap] ?; srw ?Set.mem_union=> [/lem2|/lem1] f ? <;>
  apply f=> //


@[simp]
lemma disjoint_labSet :
  Disjoint ⟪l, s⟫ ⟪l', s'⟫ = (l ≠ l' ∨ Disjoint s s') := by
  sorry

-- set_option maxHeartbeats 1600000 in
-- @[simp]
-- private lemma validSubst_sUss :
--   validSubst π (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0, ss⟫) (⟪1, s⟫ ∪ ⟪0, ss⟫ : Set _) = true := by
--   unfold π'
--   move=> dj₁ dj₂ /== [l x] /== ? l' y ?
--   checkpoint (scase: l l'=> //== /[swap] []//== <;> split_ifs=> //)
--   { move=> [] // /(Set.disjoint_left.mp dj₁) // }
--   move=> /(Set.disjoint_left.mp dj₁) //
set_option maxHeartbeats 1600000 in
private lemma hsubst_H :
  hsubst π (⟪n, s'⟫ ∪ fs) ((H₁ ∘ π) ∗↑ ⟪n,s'⟫ ∗ (H₂ ∘ π) ∗↑ fs) =
  (H₁ ∗↑ s' ∗ H₂ ∗↑ s) := by
  move: (lem1 s z n sᵢ s' disj seq)=> ?
  move: (lem2 s z n sᵢ s' disj seq)=> ?
  move: (lem3 s z n sᵢ s' disj seq)=> ?
  move: (lem4 s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s' s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s s z n sᵢ s' disj seq)=> ?
  srw -(hsubst_hhstar (s₁ := ⟪n, s'⟫) (s₂ := fs))=> //'
  { checkpoint (erw [hsubst_bighstar]; erw [hsubst_bighstar]=> //')
    srw (ssubst_s' s z n sᵢ s' disj seq) //' (ssubst_s s z n sᵢ s' disj seq) //' }
  simp; srw -disjoint_union /== => *
  move: seq disj=> ->; srw -disjoint_union=> /== //'

local notation "hsubst_H" => hsubst_H s z n sᵢ s' disj seq df dfN

private lemma π_in_s' :
  a ∈ s' -> π (n, a) = a := by
  simp=> //

private noncomputable def ι' : Int -> α -> ℤ×α :=
  fun i a =>
    if a ∈ s' then
      (n, a)
    else if a ∈ sᵢ i then
      (i, a)
    else
      (n+1, df)

local notation "ι" => ι' n sᵢ s' df

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem5 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s' ∪ sᵢ i, ∀ a' ∉ s' ∪ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ??
  move=> ? /== [] ????
  { srw ?ι' if_pos //' }
  srw ?ι' if_neg //'
  { srw if_pos //' ?if_neg //'=> [] // }
  move=> ?; apply d=> //


set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem6 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s', ∀ a' ∈ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ?? ? ? a ?;  srw ?ι' if_pos //' if_neg
  { srw ?if_pos //'; sby scase }
  move=> ?; apply (d i a)=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem9 i :
  z <= i ->
  i < n ->
  ∀ a ∈ s', ∀ a' ∉ s', ι i a ≠  ι i a' := by
  move: (disj') => d ?? ????; srw ?ι' if_pos //' if_neg //'
  scase_if=> // ? [] //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem12 i :
  z <= i ->
  i < n ->
  ∀ a ∈ sᵢ i, ∀ a' ∉ sᵢ i, ι i a ≠  ι i a' := by
  move: (disj') => d ?? ????; srw ?ι' if_neg
  { srw if_pos //'; scase_if=> [? [] //| ? ]
    srw if_neg // => [] // }
  move=> ?; apply d=> //


set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem10 i :
  validSubst (ι i) (s' ∪ sᵢ i) s' := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem11 i :
  validSubst (ι i) (s' ∪ sᵢ i) (sᵢ i) := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

-- Set.EqOn ht₁ ((ht₁ ∘ σ) ∘ ι) s'

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem7 i :
  z <= i ->
  i < n ->
  Set.EqOn f ((f ∘ π) ∘ ι i) (sᵢ i) := by
  move: (disj') => d ?? x ? /==
  srw ι' (if_neg (c := x ∈ s'))
  { srw (if_pos (c := x ∈ sᵢ i)) //' }
  move=> ?; apply d=> //


set_option maxHeartbeats 1600000 in
private lemma lem13 i :
  ssubst (ι i) (s' ∪ sᵢ i) s' = ⟪n, s'⟫ := by
  unfold ι'
  move=> ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem10=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  exists x=> //

set_option maxHeartbeats 1600000 in
private lemma lem14 i :
  z <= i ->
  i < n ->
  ssubst (ι i) (s' ∪ sᵢ i) (sᵢ i) = ⟪i, sᵢ i⟫ := by
  move: (disj') => d ?? ! [l a]
  srw fsubst_inE => /==; rotate_left
  { apply lem11=> // }
  move=> ⟨/== ? _ ?|/== -> ?⟩
  { srw ι' if_neg ?if_pos //'
    scase=> //'; move=> ?; apply d=> // }
  exists a=> //; srw ι' if_neg ?if_pos //'
  move=> ?; apply d=> //

attribute [-simp] π'

private lemma hsubst_H' :
  z <= i ->
  i < n ->
  hsubst (ι i) (s' ∪ sᵢ i) ((H₁ ∘ (ι i)) ∗↑ s' ∗ (H₂ ∘ (ι i)) ∗↑ sᵢ i) =
  (H₁ ∗↑ ⟪n,s'⟫ ∗ H₂ ∗↑ ⟪i,sᵢ i⟫) := by
  move=> h h'
  move: (lem5 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem6 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem9 z n sᵢ s' df i h h')=> ?
  move: (lem12 s z n sᵢ s' disj seq df i h h')=> ?
  -- move: (lem7 s z n sᵢ s' disj seq df i h h')=> ?
  move: (lem10 n sᵢ s' df i)=> ?
  move: (lem11 n sᵢ s' df i)=> ?
  move: (lem13 n sᵢ s' df i)=> H₁
  move: (lem14 s z n sᵢ s' disj seq df i h h')=> h₂
  srw -(hsubst_hhstar (s₁ := s') (s₂ := sᵢ i))=> //'
  { checkpoint (erw [hsubst_bighstar]; erw [hsubst_bighstar]=> //') }
  move: seq disj=> ->; srw -disjoint_union=> /== //'

local notation "hsubst_H'" => hsubst_H' s z n sᵢ s' disj seq df


set_option maxHeartbeats 1600000 in
lemma wp_for_bighop (β : Type)  [inst : Inhabited β]
  (Q : Int -> hval -> α -> hProp)
  (R R' : α -> hProp)
  (H₀ : α -> hProp)
  (Qgen : Int -> β -> α -> hProp)
  (ht : htrm) :
  z <= n ->
  (∀ j hv₁ hv₂, ∀ a ∈ s', z <= j ∧ j <= n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁ a) = (Q j hv₂ a)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ [[z,n]], ∀ a ∈ s', ∃ v, H₀ a + ∑ i in [[z, j]], Q i (hv i) a = Qgen j v a) ->
  (∀ j (v : α -> β), z <= j ∧ j < n ->
    [∗ i in s'| Qgen j (v i) i] ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' ∗↑ s' + [∗ i in s'| Qgen j (v i) i] ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗↑ s' ∗ R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩]
         (fun hv => H₀ ∗↑ s' + (∑ j in [[z, n]], Q j hv ∗↑ s') ∗ R' ∗↑ s) := by
  move=> ? eqQ gen ind *
  srw -(hsubst_H) wp_Q_eq; rotate_left 2
  { move=> ?
    rewrite [Disjoint.sum_bighstar, hhProp_add_def, bighstar_hhstar]
    srw -(hsubst_H) }
  srw -[6](ssubst_s' s z n sᵢ s' disj seq df) //'
  srw -(ssubst_s s z n sᵢ s' disj seq df) //'
  apply hsubst_wp (Q :=
    fun hv => [∗ i in ⟪n,s'⟫| H₀ (π i) ∗ ∑ j in [[z, n]], Q j (hv ∘ (j,·)) (π i)] ∗ (R' ∘ π) ∗↑ fs)=>//'
  { apply lem4=> //' }
  { move=> > hveq; congr 1; apply bighstar_eq
    move=> [] /== ? a -> /[dup]?/π_in_s'-> //'
    congr 1; apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
    move=> i ?? ; apply eqQ=> //' /= ??; apply hveq=> /==; right
    exists i }
  { move=> hv; congr 1; apply bighstar_eq=> /=
    move=> [] /== ? a -> /[dup]?/π_in_s'-> //'
    congr 1; apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
    move=> i *; apply eqQ=> //' /= ??
    unfold π'=> /=; srw if_pos //' }
  srw triple_Q_eq; rotate_left 2
  { move=> ?;
    rewrite [<-bighstar_hhstar, <-Disjoint.sum_bighstar]
    rfl }
  eapply Disjoint.wp_for_bighop (s := fs)
    (sᵢ := fun i => ⟪i, sᵢ i⟫)
    (inst := inst)
    (Qgen := fun i v a => Qgen i v a.2)
    (Q := fun i hv a => Q i (hv ∘ (i,·)) (π a)) => //'
  { move=> j ?? [] /== ? a -> /[dup]? /π_in_s'-> //' ??
    move=> hveq; apply eqQ=> //' }
  { move=> hv j ? [] /== ? a -> /[dup]? /π_in_s'-> //' }
  { simp; srw -disjoint_union /== => *
    move: seq disj=> ->; srw -disjoint_union=> /== //' }
  { move=> /== //' }
  move=> > ?
  srw -(hsubst_H') //' /= wp_Q_eq; rotate_left 2
  { move=> ?
    rewrite [hhProp_add_def, bighstar_hhstar]
    srw -(hsubst_H') //' }
  srw -(lem13 n sᵢ s' df) //' -(lem14 s z n sᵢ s') //'
  eapply hsubst_wp
    (Q := fun hv => (((fun i ↦ Q j (hv) i ∗ Qgen j (v (ι j i)) (ι j i).2)) ∗↑ s' ∗ R' ∗↑ sᵢ j))=> //'
  { apply lem5=> // }
  { move=> > hveq; congr 1; apply bighstar_eq
    move=> ??; congr 1; apply eqQ=> //' /= ??; apply hveq=> /== //' }
  { move=> hv; congr 1
    { apply bighstar_eq=> ?? /=; congr 1
      srw ι' if_pos //' π_in_s' //'
      apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
      move: (disj')=> //' }
    apply bighstar_eq=> /= ??
    srw ι' if_neg ?if_pos //'
    { srw π' /= if_pos //' }
    move: (disj')=> ?? //'}
  srw bighstar_eq
  { srw [2]bighstar_eq; apply hhimpl_trans
    apply ind (v := fun a => v (n, a))=> //'
    { srw wp2_ht_eq; apply hwp_conseq
      { move=> hv /=; srw -bighstar_hhstar hhProp_add_def
        ysimp; apply Disjoint.hhimpl_bighstar_himpl=> z ?
        srw ι' if_pos //' }
      { sdone }
      apply lem7=> // }
    move=> ??; apply Eq.symm; apply lem7=>// }
  move=> /= ??;srw ι' if_pos //'



end ForLoop

-- instance :

-- @[default_instance]
-- instance : CoeFun (α -> hProp) (fun _ => Set α -> hhProp) where
--   coe x := fun s => [∗ i in s| x i]

  -- ychange wp_align_step
  -- { srw -disjoint_union at sij'; apply sij'=> /==; omega }
  -- { move: sij'; srw sum_Ico_succl /==; omega }
  -- { simp; srw -disjoint_union=> /== *; apply dij=> /== <;> omega }
  -- { omega }
  -- { simp=> ⟨|⟩
  --   { srw -disjoint_union at sij'; apply sij'=> /==; omega }
  --   move: sij'; srw sum_Ico_succl /==; omega }
  -- { omega }
  -- ychange ind
  -- { simpNums; omega }
  -- apply hwp_conseq=> hv /==
  -- -- scase: [i = n]=> [?|->]
  -- ychange (ih (s := ∑ i ∈ [[i, n]], sᵢ i)) <;> try trivial
  -- { move: sij'; srw sum_Ico_succl /==; omega }
  -- { omega }
  -- { move=> ???? /Heq; sapply; omega }
  -- apply hwp_conseq=> hv' /=
  -- srw -fun_insert_assoc [2]sum_Ico_predr=> [//|]
  -- omega


end LGTM
