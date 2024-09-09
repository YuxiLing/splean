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
import Lgtm.Unary.SepLog
import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.Subst

open Classical trm val prim
open SetSemiring

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

instance : AddCommMonoid (Set α) := SetSemiring.instAddCommMonoid
attribute [-simp] hhProp_add_def

-- open BigOperators

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

-- namespace LGTM

namespace Disjoint

section ForLoop

lemma LGTM.wp_for_aux
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
    srw Finset.Ico_self /== LGTM.wp_cons /=
    ychange hwp_for'=> /==
    srw LGTM.wp /== hwp0_dep; ysimp[hv₀]
    apply Heq=> // }
  move=> i ? ih hv₀ ? sij' seq ? Heq
  srw LGTM.wp_cons /=; ychange hwp_for=> /==
  { omega }
  { sdone }
  srw -(LGTM.wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ (_ ∪__ x)))
  srw sum_Ico_succl
  ychange LGTM.wp_align_step_disj
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
lemma LGTM.wp_for (Inv : Int -> hval -> hhProp) (sᵢ : Int -> Set α) (ht : htrm) :
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
     ychange (LGTM.wp_for_aux (sᵢ := sᵢ) (i := z) (z := z) (n := n))=> //
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

lemma choose_fun2 {α β γ : Type}  [Inhabited β] [Inhabited γ]
   (p : α -> β -> γ -> Prop) (s : Set α) :
  (∀ a ∈ s, ∃ b c, p a b c) -> (∃ (f : α -> β) (g : α -> γ), (∀ a ∈ s, p a (f a) (g a))) := by
  move=> pH
  shave: (∀ a ∈ s, ∃ (bc : β×γ), p a bc.fst bc.snd)
  { move=> ? /pH ![b c] ?; exists (b,c)=> //  }
  move=> /choose_fun /(_ ((default : β), (default : γ)))[f] ?
  exists (f · |>.fst), (f · |>.snd)

set_option maxHeartbeats 1600000 in
lemma LGTM.wp_for_bighop (β : Type) [inst : Inhabited β]
  (z n : Int)
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  s = ∑ i in [[z, n]], sᵢ i ->
  (∀ (hv : hval), ∀ j ∈ [[z,n]], ∃ v H, H₀ + ∑ i in [[z, j]], Q i hv = Qgen j v ∗ H) ->
  Disjoint s' s ->
  (∀ i j, i != j -> z <= i ∧ i < n -> z <= j ∧ j < n -> Disjoint (sᵢ i) (sᵢ j)) ->
  (∀ j v, z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗ R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> ? eqQ ? gen dj dij' ind *
  eapply wp_for
    (hv₀ := fun _ => default)
    (Inv := fun i hv =>
      H₀ +
      (∑ j in [[z, i]], Q j hv) ∗
       Inv i ∗
      ((∑ j in [[z, i]], R' ∗↑ sᵢ j) ∗ (∑ j in [[i, n]], R ∗↑ sᵢ j)))=> //'
  { move=> > ? hveq; ysimp;-- srw ?sum_bighstar; apply hhimpl_bighstar_himpl=> a ?
    srw (Finset.sum_congr (s₂ := [[z,j]])); rotate_right 2
    { move=> /== k ??; apply eqQ
      { auto }
      move=> ??; apply hveq=> xin
      sapply: (Set.disjoint_left.mp dj xin)
      srw mem_union; exists k=> ⟨|//⟩ /==; omega }
    all_goals auto }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' hhProp_add_def
    ychange ind=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    -- srw -gen //'
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp
    srw sum_Ico_predr //' /== hhProp_add_def hhstar_comm eqQ; ysimp=> //'
    srw -gen //' hhProp_add_def; ysimp
    srw Finset.sum_congr; apply hhimpl_refl=> //'
    move=> /== k ??; apply eqQ=> //' ? f /==
    specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
    move: (Set.disjoint_left.mp dij' f)=> //'  }
  { srw Finset.Ico_self /== //'; subst_vars; srw -sum_bighstar_set hhProp_add_def
    ysimp }
  move=> hv' /=; subst_vars; srw sum_bighstar_set Finset.Ico_self /==;
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
    { move=> ?? hv₀ ->/==; srw LGTM.wp /== hwp0_dep; ysimp[hv₀]
      apply Inveq=> // }
    move=> j ? ih ? s hv₀ ->
    srw sum_Ico_succl /==; intros _ dij=> //
    srw -(fun_insert_ff (s := sᵢ (j - 1)) (f := ht))
    srw -LGTM.wp_unfold_first
    ychange ind
    { sby simpNums }
    { srw -disjoint_union=> /== *; apply disj=> /== <;> omega }
    simp; srw ?LGTM.wp_cons /=; apply hwp_conseq
    { move=> hv /=; srw LGTM.wp /== hwp0_dep; ysimp=> ?
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
      srw LGTM.wp_cons /=; ychange hwp_while=> //
      ychange cndE=> //; apply hwp_conseq=> hv /=
      ysimp; ychange hwp_if
      apply htriple_val
      apply hhimpl_trans; apply LGTM.wp_while_aux_false=> //
      apply hwp_conseq=> ? /=; apply Inveq=> // }
    move: i L₂ L₁ s hv₀  seq
    apply Int.le_induction_down
    { move=> ???? ->/==; ychange cndn=> // }
    move=> j ? ind ? s dij hv₀ ?
    srw LGTM.wp_cons /=; ychange hwp_while=> //
    -- { sorry }
    ychange cndE
    { sby simpNums }
    apply hwp_conseq=> hv /=
    ysimp; ychange hwp_if
    srw -(LGTM.wp_cons (sht := ⟨_, _⟩) (Q := fun x ↦ Inv _ _ (_ ∪__ x)))
    srw sum_Ico_succl
    ychange LGTM.wp_align_step_disj
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
    { srw LGTM.wp_cons /=;
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
    { sby apply LGTM.wp_conseq=> ? }
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

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q
set_option maxHeartbeats 1600000 in
lemma LGTM.wp_while_bighop (β : Type) [inst : Inhabited β]
  (z n : Int)
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Bool -> Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (sᵢ : Int -> Set α)
  (ht : htrm) :
  -- s'.Nonempty ->
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  s = ∑ i in [[z, n]], sᵢ i ->
  (∀ (hv : hval), ∀ j ∈ [[z,n]], ∃ v H, H₀ + ∑ i in [[z, j]], Q i hv = Qgen j v ∗ H) ->
  Disjoint s' s ->
  (∀ (i j : ℤ), (i != j) = true → z ≤ i ∧ i < n → z ≤ j ∧ j < n → Disjoint (sᵢ i) (sᵢ j)) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv true j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
          fun hv' =>
          Q j hv' + Qgen j v ∗ (∃ʰ b, (Inv b (j + 1))) ∗ R' ∗↑ (sᵢ j)) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (sᵢ j)) ==>
    LGTM.wp
          [⟨sᵢ j, ht⟩]
          (fun hv' => Q j hv' + Qgen j v ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (sᵢ j)))) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => ⌜(bv = fun _ => val.val_bool b)⌝ ∗ Inv b j)) ->
  (∀ b, Inv b n ==> ⌜b = false⌝ ∗ Inv b n) ->
  H₀ ∗ Inv b₀ z ∗ R ∗↑ s ==>
    LGTM.wp [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩]
      fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv false n ∗ R' ∗↑ s := by
  move=> ? eqQ ? gen dj dij' indt indf cndE cndn
  eapply LGTM.wp_while
    (z := z)
    (n := n)
    (hv₀ := fun _ => default)
    (Inv := fun b i hv =>
      H₀ +
      (∑ j in [[z, i]], Q j hv) ∗
       Inv b i ∗
      ((∑ j in [[z, i]], R' ∗↑ sᵢ j) ∗ (∑ j in [[i, n]], R ∗↑ sᵢ j)))=> //'
  { move=> > ? hveq; ysimp
    srw (Finset.sum_congr (s₂ := [[z,j]])); rotate_right 2
    { move=> /== k ??; apply eqQ
      { auto }
      move=> ??; apply hveq=> xin
      sapply: (Set.disjoint_left.mp dj xin)
      srw mem_union; exists k=> ⟨|//⟩ /==; omega }
    all_goals auto }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' hhProp_add_def
    ychange indt=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    -- srw -gen //'
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp
    srw sum_Ico_predr //' /== hhProp_add_def hhstar_comm eqQ; ysimp=> //'
    srw -gen //' hhProp_add_def; ysimp
    srw Finset.sum_congr; apply hhimpl_refl=> //'
    move=> /== k ??; apply eqQ=> //' ? f /==
    specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
    move: (Set.disjoint_left.mp dij' f)=> //'  }
  { move=> j hv ?
    specialize gen hv=> //'
    move: gen=> /choose_fun2
    scase! => v H' /== /[dup] gen -> //'
    srw //' [2]sum_Ico_succl //' hhProp_add_def
    ychange indf=> //'; apply hhimpl_trans; apply LGTM.wp_frame; apply hwp_conseq=> hv' /=
    -- srw -gen //'
    srw [4]sum_Ico_predr //' /== ?hhProp_add_def; ysimp
    srw sum_Ico_predr //' /== hhProp_add_def hhstar_comm eqQ; ysimp=> //'
    srw -gen //' hhProp_add_def; ysimp
    srw Finset.sum_congr; apply hhimpl_refl=> //'
    move=> /== k ??; apply eqQ=> //' ? f /==
    specialize dij' k j ?_ ?_ ?_=> //'; simp; omega
    move: (Set.disjoint_left.mp dij' f)=> //'  }
  { move=> > ?; specialize cndE j b
    srw -hwp_equiv at cndE; ychange cndE=> //'
    apply hhimpl_trans; apply hwp_frame;
    apply hwp_conseq=> ?; ysimp }
  { move=> ??; ychange cndn; ysimp }
  { srw Finset.Ico_self /== -sum_bighstar_set hhProp_add_def; ysimp; ysimp }
  move=> ? /=; srw Finset.Ico_self -sum_bighstar_set /==; ysimp; ysimp

end WhileLoop

end Disjoint

namespace ForLoopAux

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

private noncomputable def κ' : α -> ℤ × α :=
  fun a => if a ∈ s' then (n, a) else (n+1, df)


local notation "π" => π' z n sᵢ s' df
local notation "κ" => κ' n s' df

attribute [simp] π' κ' mem_union

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

lemma inj_κ : Set.InjOn κ s' := by
  move=> ?? ?? /==; srw ?if_pos //

lemma fsubst_set_union (σ : α -> β) :
  hlocal s₁ h ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  fsubst σ (s₁ ∪ s₂) h = fsubst σ s₁ h := by
  move=> l neq !z
  srw ?fsubst ?partialInvSet
  scase: [∃ a ∈ s₁ ∪ s₂, σ a = z]=> /==
  { move=> ?; srw dif_neg // dif_neg // }
  move=> x [] xin <-
  { srw dif_pos // dif_pos /==; rotate_left
    { sby exists x }
    congr=> !y !⟨|⟩//== [] // /neq /(_ xin) // }
  srw dif_pos //; rotate_left
  { exists x=> // }
  srw /== dif_neg //==; apply l
  move=> /neq /(_ xin); sapply
  generalize heq : (choose _) = y
  shave: (y ∈ s₁ ∨ y ∈ s₂) ∧ σ y = σ x
  { srw -heq; apply choose_spec (p := fun y => (y ∈ s₁ ∨ y ∈ s₂) ∧ σ y = σ x)  }
  move=> //

private lemma vsκ :
  validSubst κ s' h := by move=> ????/=; srw ?if_pos //

private lemma vsπ (h : hheap α) :
  validSubst π ⟪n, s'⟫ (fsubst κ s' h) := by
  move=> [] /== ? a -> ? ? b -> ?
  srw if_neg //' if_pos //' if_pos //'

private lemma hE (h : hheap α) :
  hlocal s' h ->
  h = (fsubst π (⟪n, s'⟫ ∪ fs) (fsubst κ s' h)) := by
  move=> ?
  srw fsubst_set_union
  { move=> !a; scase: [a ∈ s']
    { move=> ?; srw (fsubst_local_out (s' := ⟪n,s'⟫)) //
      { move=> [m x] /== ?; apply fsubst_local_out => //
        { apply vsκ }
        srw fsubst_inE /== => ??; srw if_pos //' => [] //' }
      { apply vsπ }
      srw fsubst_inE /== => ?? -> ?
      srw if_neg //' ?if_pos //' => ? // }
    move=> ?
    shave aeq: a = π (κ a)
    { srw κ' if_pos //' }
    srw [2]aeq ?fsubst_σ //
    { apply vsκ }
    { apply vsπ }
    srw /== if_pos // }
  { move=> [m x] /== ?; apply fsubst_local_out => //
    { apply vsκ }
    srw fsubst_inE /== => ??; srw if_pos //' => [] //' }
  apply lem3=> //

lemma hsubst_πκ :
  hhlocal s' H₁ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁) = H₁ := by
  move=> lh !h !⟨![h -> ![h ->] ?? _ ]|?⟩
  { srw -hE // }
  exists (fsubst κ s' h)=> ⟨|⟨|⟩⟩
  { apply hE=> // }
  { exists h=> ⟨//|⟨//|⟩⟩; apply vsκ }
  move=> a; srw ?Set.mem_union=> [] ain b []
  { apply vsπ=> // }
  { move=> /lem3/(_ ain) /[apply] /(_ disj) /(_ seq) /(_ dfN) // }
  { move=> *; exfalso; eapply lem3=> // }
  move=> bin; srw ?fsubst_local_out //'
  { apply vsκ }
  { srw fsubst_inE /== => ??; srw if_pos
    scase: b bin=> /== // }
  { apply vsκ }
  srw fsubst_inE /== => ??; srw if_pos
  scase: a ain=> /== //


set_option maxHeartbeats 1600000 in
private lemma hsubst_H_aux :
  hhlocal s' H₁ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁ ∗ (H₂ ∘ π) ∗↑ fs) =
  (H₁ ∗ H₂ ∗↑ s) := by
  move=> ?
  move: (lem1 s z n sᵢ s' disj seq)=> ?
  move: (lem2 s z n sᵢ s' disj seq)=> ?
  move: (lem3 s z n sᵢ s' disj seq)=> ?
  move: (lem4 s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s' s z n sᵢ s' disj seq)=> ?
  move: (validSubst_s s z n sᵢ s' disj seq)=> ?
  srw -(hsubst_hhstar (s₁ := ⟪n, s'⟫) (s₂ := fs))=> //'
  { erw [hsubst_bighstar]=> //'
    srw (hsubst_πκ s z n sᵢ s' disj seq)=> //'
    srw (ssubst_s s z n sᵢ s' disj seq)=> //'  }
  { simp; srw -disjoint_union /== => *
    move: seq disj=> ->; srw -disjoint_union=> /== //' }
  move=> ? ![h -> ??] [m a] /== ?
  srw fsubst_local_out //' fsubst_inE /==
  move=> ??; srw if_pos => //' [] //'

set_option maxHeartbeats 1600000 in
private lemma hsubst_H :
  hhlocal s' H₁ ->
  hhlocal s' H₂ ->
  hsubst π (⟪n, s'⟫ ∪ fs) (hsubst κ s' H₁ ∗ hsubst κ s' H₂ ∗ (H₃ ∘ π) ∗↑ fs) =
  (H₁ ∗ H₂ ∗ H₃ ∗↑ s) := by
  move=> ??
  srw -?hhstar_assoc  -(hsubst_H_aux s z n sᵢ s' disj seq df dfN)
  { srw hsubst_hhstar_same //' => ???? /==
    srw ?if_pos // }
  srw hhlocal_hhstar //


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

lemma fsubst_ι' i :
  z <= i ->
  i < n ->
  hlocal s' H₁ ->
  fsubst (ι i) (s' ∪ sᵢ i) H₁ = fsubst (ι i) s' H₁ := by
  move=> ???; srw fsubst_set_union //
  apply lem6=> //

lemma fsubst_κι i :
  z <= i ->
  i < n ->
  hlocal s' H₁ ->
  fsubst κ s' H₁ = fsubst (ι i) (s' ∪ sᵢ i) H₁ := by
  move=> ?? l ! [m a]
  srw (fsubst_ι' s z n) //'
  srw ?fsubst ?partialInvSet
  split_ifs <;> rename_i h₁ h₂=> /==
  { congr=> !b ! /== ?; srw if_pos // => ⟨[]|<-⟩
    { srw ι' if_pos // }
    srw ι' if_pos // }
  { exfalso; move: h₁ h₂=> /== ?? //
    srw if_pos //' => []; exists a=> ⟨//|⟩
    srw ι' if_pos // }
  exfalso; move: h₂ h₁=> /== ?? //
  srw ι' if_pos //' => []; exists a=> ⟨//|⟩
  srw if_pos //


lemma hsubst_κι i :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hsubst κ s' H₁ = hsubst (ι i) (s' ∪ sᵢ i) H₁ := by
  move=> ?? l !h ! ⟨|⟩ ![] h -> Hh ?
  { srw (fsubst_κι (i := i)) //; exists h=> ⟨//|⟨//|⟩⟩
    move=> ?; srw ?Set.mem_union=> [] ? ? [] ?
    { srw ?ι' ?if_pos // }
    { move=> *; exfalso; apply lem6 => // }
    { move=> *; exfalso; apply lem6 => // }
    srw ?(l _ Hh) //'
    { move: seq disj=> ->; srw -disjoint_union => dj
      specialize dj i ?_=> //'
      srw Set.disjoint_left at dj=> // }
    move: seq disj=> ->; srw -disjoint_union => dj
    specialize dj i ?_=> //'
    srw Set.disjoint_left at dj=> // }
  srw -(fsubst_κι (i := i)) //; exists h=> ⟨//|⟨//|⟩⟩
  move=> ????; srw ?κ' ?if_pos //

attribute [-simp] π'

private lemma hsubst_H'_aux :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hsubst (ι i) (s' ∪ sᵢ i) (H₁ ∗ (H₂ ∘ (ι i)) ∗↑ sᵢ i) =
  (hsubst (ι i) (s' ∪ sᵢ i) H₁ ∗ H₂ ∗↑ ⟪i,sᵢ i⟫) := by
  move=> h h' ?
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
  { erw [hsubst_bighstar]=> //' }
  move: seq disj=> ->; srw -disjoint_union=> /== //'

private lemma hsubst_H' :
  z <= i ->
  i < n ->
  hhlocal s' H₁ ->
  hhlocal s' H₂ ->
  hsubst (ι i) (s' ∪ sᵢ i) (H₁ ∗ H₂ ∗ (H₃ ∘ (ι i)) ∗↑ sᵢ i) =
  (hsubst (ι i) (s' ∪ sᵢ i) H₁ ∗ hsubst (ι i) (s' ∪ sᵢ i) H₂ ∗ H₃ ∗↑ ⟪i,sᵢ i⟫) := by
  move=> ?? ??
  srw -?hhstar_assoc (hsubst_hhstar_same _ s' (s' ∪ sᵢ i)) //'
  { srw -(hsubst_H'_aux s z n sᵢ s' disj seq df) // }
  { move=> ????; srw ?ι' ?if_pos // }
  apply lem9=> //

local notation "hsubst_H'" => hsubst_H' s z n sᵢ s' disj seq df

-- private lemma hsubst_H'' (β : Type) (H₂ : β -> _) :
--   z <= i ->
--   i < n ->
--   hsubst (ι i) (s' ∪ sᵢ i) ((H₁ ∘ (ι i)) ∗↑ s' ∗ (∃ʰ x, (H₂ x ∘ (ι i)) ∗↑ s') ∗ (H₃ ∘ (ι i)) ∗↑ sᵢ i) =
--   (H₁ ∗↑ ⟪n,s'⟫ ∗ (∃ʰ x, H₂ x ∗↑ ⟪n,s'⟫) ∗ H₃ ∗↑ ⟪i,sᵢ i⟫) := by
--   move=> h h'
--   move: (lem5 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem6 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem9 z n sᵢ s' df i h h')=> ?
--   move: (lem12 s z n sᵢ s' disj seq df i h h')=> ?
--   -- move: (lem7 s z n sᵢ s' disj seq df i h h')=> ?
--   move: (lem10 n sᵢ s' df i)=> ?
--   move: (lem11 n sᵢ s' df i)=> ?
--   move: (lem13 n sᵢ s' df i)=> ?
--   move: (lem14 s z n sᵢ s' disj seq df i h h')=> h₂
--   srw -hhstar_assoc [2]hhstar_comm hhstar_hhexists_l
--   srw -(hsubst_hhstar (s₁ := s') (s₂ := sᵢ i))=> //'
--   { erw [hsubst_bighstar];
--     simp_rw [bighstar_hhstar]
--     erw [hsubst_hhexists]=> //'
--     srw h₂ -hhstar_assoc [3]hhstar_comm [2]hhstar_hhexists_l;
--     congr; apply congr_arg=> !x
--     erw [hsubst_bighstar (H := (fun i_1 ↦ (H₂ x) i_1 ∗ (H₁) i_1))]
--     simp_rw [bighstar_hhstar]=> // }
--   move: seq disj=> ->; srw -disjoint_union=> /== //'

-- local notation "hsubst_H''" => hsubst_H'' s z n sᵢ s' disj seq df

lemma LGTM.triple_Q_eq :
  (∀ hv, Q hv = Q' hv) ->
  LGTM.triple sht H Q = LGTM.triple sht H Q' := by
  sby move=> /LGTM.hwp_Q_eq=> eq; srw ?LGTM.triple ?LGTM.wp eq

lemma wp2_ht_eq :
  Set.EqOn ht₁ ht₁' s₁ ->
  Set.EqOn ht₂ ht₂' s₂ ->
  LGTM.wp [⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩] Q =
  LGTM.wp [⟨s₁, ht₁'⟩, ⟨s₂, ht₂'⟩] Q := by sorry

lemma wp1_ht_eq :
  Set.EqOn ht₂ ht₂' s₂ ->
  LGTM.wp [⟨s₂, ht₂⟩] Q =
  LGTM.wp [⟨s₂, ht₂'⟩] Q := by sorry

lemma hlocal_fsubst_κ :
  hlocal s' H ->
  hlocal (⟪n, s'⟫ ∪ fs) (fsubst κ s' H) := by
  move=> hl h ?; srw fsubst_local_out //'
  { apply vsκ }
  srw fsubst_inE /== => ??; srw if_pos //'=> []//

lemma hhlocal_hsubst_κ :
  hhlocal s' H ->
  hhlocal (⟪n, s'⟫ ∪ fs) (hsubst κ s' H) := by
  move=> hl h ![h -> ??]; apply hlocal_fsubst_κ=> //

set_option maxHeartbeats 1600000 in
lemma wp_for_bighop_aux (β : Type)  [inst : Inhabited β]
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  hhlocal s' H₀ ->
  (∀ i, hhlocal s' (Inv i)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  z <= n ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ [[z,n]], ∃ v H, H₀ + ∑ i in [[z, j]], Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗  R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> lH₀ lInv lQ lgen ? eqQ gen ind *
  srw -(hsubst_H) //' LGTM.wp_Q_eq; rotate_left 2
  { move=> ?; srw -(hsubst_H) //' hhProp_add_def //' }
  srw -[8](ssubst_s' s z n sᵢ s' disj seq df) //'
  srw -(ssubst_s s z n sᵢ s' disj seq df) //'
  apply hsubst_wp (Q :=
    fun hv => hsubst κ s' (H₀ ∗ ∑ j in [[z, n]], Q j (hv ∘ (j,·))) ∗ hsubst κ s' (Inv n) ∗ (R' ∘ π) ∗↑ fs)=>//'
  { apply lem4=> //' }
  { simp=> ⟨|⟩ <;> apply hhlocal_hsubst_κ=> //' }
  { move=> > hveq; congr! 3
    apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
    move=> i ?? ; apply eqQ=> //' /= ??; apply hveq=> /==; right
    exists i }
  { move=> hv; congr! 3; apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
    move=> i *; apply eqQ=> //' /= ??
    unfold π'=> /=; srw if_pos //' }
  srw LGTM.triple_Q_eq; rotate_left
  { move=> hv;
    rewrite [<-hsubst_hhstar_same κ s']
    rewrite [hsubst_hhstar_sum_same]
    rfl
    all_goals auto
    { move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  eapply Disjoint.LGTM.wp_for_bighop (s := fs)
    (sᵢ := fun i => ⟪i, sᵢ i⟫)
    (inst := inst)
    (Inv := fun i => hsubst κ s' (Inv i))
    (Qgen := fun i v =>  hsubst κ s' $ Qgen i v)
    (Q := fun i hv =>  hsubst κ s' $ Q i (hv ∘ (i,·))) => //'
  { move=> > /== ?? hveq; apply congr_arg; apply eqQ=> //' }
  { move=> hv j /gen /(_ (fun i => hv ∘ (i, ·))) ![v H] eq
    exists v, (hsubst κ s' H);
    srw hsubst_hhstar_same //'; rotate_left
    { shave /==: hhlocal s' (Qgen j v ∗ H)
      srw -eq hhProp_add_def //= }
    { move=> ????; srw ?κ' ?if_pos // }
    srw -eq ?hhProp_add_def -hsubst_hhstar_same //'
    { srw hsubst_hhstar_sum_same //'
      move=> ????; srw ?κ' ?if_pos // }
    move=> ????; srw ?κ' ?if_pos // }
  { simp; srw -disjoint_union /== => *
    move: seq disj=> ->; srw -disjoint_union=> /== //' }
  { move=> /== //' }
  move=> > ?
  srw ?(hsubst_κι s z n sᵢ (i := j)) //' LGTM.wp_Q_eq; rotate_left 2
  { move=> ?; srw (hsubst_κι s z n sᵢ (i := j)) //'  }
  srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
  { move=> ?
    rewrite [hhProp_add_def, hsubst_hhstar_same _ s']
    { srw -(hsubst_H') //' }
    all_goals auto
    {  move=> ????; srw ?ι' ?if_pos // }
    apply lem9=> //' }
  srw -(lem13 n sᵢ s' df) //' -(lem14 s z n sᵢ s') //'
  eapply hsubst_wp
    (Q := fun hv => ((Q j hv ∗ Qgen j v) ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j))=> //'
  { apply lem5=> // }
  { srw ?hhlocal_hhstar=> /== ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
  { move=> > hveq; congr 2; apply eqQ=> //' /= ??; apply hveq=> /== //' }
  { move=> hv; congr! 2
    { apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
      move: (disj')=> //' }
    apply bighstar_eq=> /= ??
    srw ι' if_neg ?if_pos //'
    { srw π' /= if_pos //' }
    move: (disj')=> ?? //' }
  srw bighstar_eq
  { apply hhimpl_trans
    apply ind (v := v)=> //'
    srw wp2_ht_eq; apply hwp_conseq
    { move=> hv /=; srw hhProp_add_def
      ysimp }
    { sdone }
    apply lem7=> // }
  move=> ??; apply Eq.symm; apply lem7=>//


lemma labSet_nonempty :
  s'.Nonempty ->
  ⟪n, s'⟫.Nonempty := by scase=> w ? ⟨⟨|⟩|//⟩

-- set_option maxHeartbeats 1600000 in
-- lemma LGTM.wp_while_bighop_aux [Inhabited α] (β : Type) [inst : Inhabited β]
--   (Q : Int -> hval -> α -> hProp)
--   (R R' : α -> hProp)
--   (H₀ : α -> hProp)
--   (Inv : Bool -> Int -> α -> hProp)
--   (Qgen : Int -> β -> α -> hProp)
--   (ht : htrm) :
--   s'.Nonempty ->
--   z <= n ->
--   (∀ j hv₁ hv₂, ∀ a ∈ s', z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁ a) = (Q j hv₂ a)) ->
--   s = ∑ i in [[z, n]], sᵢ i ->
--   (∀ (hv : Int -> hval), ∀ j ∈ [[z,n]], ∀ a ∈ s', ∃ v, H₀ a + ∑ i in [[z, j]], Q i (hv i) a = Qgen j v a) ->
--   Disjoint s' s ->
--   (∀ j (v : α -> β), z <= j ∧ j < n ->
--     [∗ i in s'| Qgen j (v i) i] ∗ (Inv true j ∗↑ s') ∗ (R ∗↑ (sᵢ j)) ==>
--     LGTM.wp
--           [⟨s', fun _ => c⟩, ⟨sᵢ j, ht⟩]
--           (fun hv' =>
--           Q j hv' ∗↑ s' + [∗ i in s'| Qgen j (v i) i] ∗ (∃ʰ b, (Inv b (j + 1) ∗↑ s')) ∗ (R' ∗↑ (sᵢ j)))) ->
--   (∀ j (v : α -> β), z <= j ∧ j < n ->
--     [∗ i in s'| Qgen j (v i) i] ∗ (Inv false j ∗↑ s') ∗ (R ∗↑ (sᵢ j)) ==>
--     LGTM.wp
--           [⟨sᵢ j, ht⟩]
--           (fun hv' => Q j hv' ∗↑ s' + [∗ i in s'| Qgen j (v i) i] ∗ (Inv false (j + 1) ∗↑ s')) ∗ (R' ∗↑ (sᵢ j))) ->
--   (∀ j b, ∀ a ∈ s', z <= j ∧ j <= n ->
--     triple cnd (Inv b j a) (fun bv => hpure (bv = val.val_bool b) ∗ Inv b j a)) ->
--   (∀ b, ∀ a ∈ s', himpl (Inv b n a) (hpure (b = false) ∗ Inv b n a)) ->
--   H₀ ∗↑ s' ∗ Inv b₀ z ∗↑ s' ∗ R ∗↑ s ==>
--     LGTM.wp [⟨s', fun _ => trm_while cnd c⟩, ⟨s, ht⟩]
--       fun hv => H₀ ∗↑ s' + (∑ j in [[z, n]], Q j hv ∗↑ s') ∗ Inv false n ∗↑ s' ∗ R' ∗↑ s := by
--   move=> ?? eqQ ? gen ? indt indf *
--   srw -(hsubst_H) LGTM.wp_Q_eq; rotate_left 2
--   { move=> ?
--     rewrite [Disjoint.sum_bighstar, hhProp_add_def, bighstar_hhstar]
--     srw -(hsubst_H) }
--   srw -[8](ssubst_s' s z n sᵢ s' disj seq df) //'
--   srw -(ssubst_s s z n sᵢ s' disj seq df) //'
--   apply hsubst_wp (Q :=
--     fun hv => [∗ i in ⟪n,s'⟫| H₀ (π i) ∗ ∑ j in [[z, n]], Q j (hv ∘ (j,·)) (π i)] ∗ (Inv false n ∘ π) ∗↑ ⟪n, s'⟫ ∗ (R' ∘ π) ∗↑ fs)=>//'
--   { apply lem4=> //' }
--   { move=> > hveq; congr 1; apply bighstar_eq
--     move=> [] /== ? a -> /[dup]?/π_in_s'-> //'
--     congr 1; apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
--     move=> i ?? ; apply eqQ=> //' /= ??; apply hveq=> /==; right
--     exists i }
--   { move=> hv; congr 1; apply bighstar_eq=> /=
--     move=> [] /== ? a -> /[dup]?/π_in_s'-> //'
--     congr 1; apply Finset.sum_congr (s₂ := [[z, n]])=> [//|]/==
--     move=> i *; apply eqQ=> //' /= ??
--     unfold π'=> /=; srw if_pos //' }
--   srw LGTM.triple_Q_eq; rotate_left
--   { move=> ?;
--     rewrite [<-bighstar_hhstar, <-Disjoint.sum_bighstar]
--     rfl }
--   eapply Disjoint.LGTM.wp_while_bighop (s := fs)
--     (sᵢ := fun i => ⟪i, sᵢ i⟫)
--     (inst := inst)
--     (Inv := fun b i => Inv b i ∘ π)
--     (Qgen := fun i v a => Qgen i v a.2)
--     (Q := fun i hv a => Q i (hv ∘ (i,·)) (π a)) => //'
--   { apply labSet_nonempty=> // }
--   { move=> j ?? [] /== ? a -> /[dup]? /π_in_s'-> //' ??
--     move=> hveq; apply eqQ=> //' }
--   { move=> hv j ? [] /== ? a -> /[dup]? /π_in_s'-> //' }
--   { simp; srw -disjoint_union /== => *
--     move: seq disj=> ->; srw -disjoint_union=> /== //' }
--   { move=> /== //' }
--   { move=> > ?
--     srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
--     { move=> ?
--       rewrite [hhProp_add_def, bighstar_hhstar]
--       srw -(hsubst_H'') //' }
--     srw -(lem13 n sᵢ s' df) //' -(lem14 s z n sᵢ s') //'
--     eapply hsubst_wp
--       (Q := fun hv => (((fun i ↦ Q j (hv) i ∗ Qgen j (v (ι j i)) (ι j i).2)) ∗↑ s' ∗ (∃ʰ b, Inv b (j+1) ∗↑ s') ∗ R' ∗↑ sᵢ j))=> //'
--     { apply lem5=> // }
--     { move=> > hveq; congr 1; apply bighstar_eq
--       move=> ??; congr 1; apply eqQ=> //' /= ??; apply hveq=> /== //' }
--     { move=> hv; congr 2
--       { apply bighstar_eq=> ?? /=; congr 1
--         srw ι' if_pos //' π_in_s' //'
--         apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
--         move: (disj')=> //' }
--       { apply congr_arg=> !x
--         apply bighstar_eq=> /= ??
--         srw ι' if_pos //'  π_in_s' //' }
--       apply bighstar_eq=> /= ??
--       srw ι' if_neg ?if_pos //'
--       { srw π' /= if_pos //' }
--       move: (disj')=> ?? //'}
--     srw bighstar_eq
--     { srw [2]bighstar_eq
--       { srw [3]bighstar_eq
--         apply hhimpl_trans
--         apply indt (v := fun a => v (n, a))=> //'
--         { srw wp2_ht_eq; apply hwp_conseq
--           { move=> hv /=; srw -bighstar_hhstar hhProp_add_def
--             ysimp=> ?; apply Disjoint.hhimpl_bighstar_himpl=> z ?
--             srw ι' if_pos //' }
--           { sdone }
--           apply lem7=> // }
--         move=> ??; apply Eq.symm; apply lem7=>// }
--       move=> ?? /=
--       srw ι' if_pos //'  π_in_s' //' }
--     move=> /= ??;srw ι' if_pos //' }
--   { move=> > ?
--     srw -(hsubst_H') //' /= LGTM.wp_Q_eq; rotate_left 2
--     { move=> ?
--       rewrite [hhProp_add_def, bighstar_hhstar]
--       srw -(hsubst_H') //' }
--     srw -(lem14 s z n sᵢ s') //'
--     eapply hsubst_wp1
--       (Q := fun hv => (((fun i ↦ Q j (hv) i ∗ Qgen j (v (ι j i)) (ι j i).2)) ∗↑ s' ∗ (Inv false (j+1) ∗↑ s') ∗ R' ∗↑ sᵢ j))=> //'
--     { apply lem5=> // }
--     {  }
--     { move=> > hveq; congr 1; apply bighstar_eq
--       move=> ??; congr 1; apply eqQ=> //' /= ??; apply hveq=> /== //' }
--     { move=> hv; congr 2
--       { apply bighstar_eq=> ?? /=; congr 1
--         srw ι' if_pos //' π_in_s' //'
--         apply eqQ=> //' /= ??; srw ι' if_neg ?if_pos //' => ?
--         move: (disj')=> //' }
--       { apply bighstar_eq=> /= ??
--         srw ι' if_pos //'  π_in_s' //' }
--       apply bighstar_eq=> /= ??
--       srw ι' if_neg ?if_pos //'
--       { srw π' /= if_pos //' }
--       move: (disj')=> ?? //'}
--     srw bighstar_eq
--     { srw [2]bighstar_eq
--       { srw [3]bighstar_eq
--         apply hhimpl_trans
--         apply indt (v := fun a => v (n, a))=> //'
--         { srw wp2_ht_eq; apply hwp_conseq
--           { move=> hv /=; srw -bighstar_hhstar hhProp_add_def
--             ysimp=> ?; apply Disjoint.hhimpl_bighstar_himpl=> z ?
--             srw ι' if_pos //' }
--           { sdone }
--           apply lem7=> // }
--         move=> ??; apply Eq.symm; apply lem7=>// }
--       move=> ?? /=
--       srw ι' if_pos //'  π_in_s' //' }
--     move=> /= ??;srw ι' if_pos //' }

end ForLoopAux

variable (z n : ℤ)
variable (sᵢ : ℤ -> Set α)
variable (s' : Set α)
variable (disj : Disjoint s' s)
variable (seq: s = ∑ i in [[z, n]], sᵢ i)

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

private lemma lem_s' [Inhabited α] :
  z <= i ->
  i < n ->
  ssubst some (s' ∪ s) s' =
  ssubst some (s' ∪ sᵢ i) s' := by
  move=> ?? !x /== ⟨|⟩ /==//

private lemma lem_s [Inhabited α] :
  z <= i ->
  i < n ->
  ssubst some (s' ∪ s) (sᵢ i) =
  ssubst some (s' ∪ sᵢ i) (sᵢ i) := by
  move=> ?? !x /== ⟨|⟩ /==// ? -> _ ? ⟨|⟨//|⟨|//⟩⟩⟩
  right; srw seq /==; exists i=> //'

private lemma lem_fsubst [Inhabited α] :
  z <= i ->
  i < n ->
  hlocal s' H ->
  fsubst some (s' ∪ s) H = fsubst some (s' ∪ sᵢ i) H := by
  move=> *;
  apply Eq.symm; apply fsubst_subset_set_local=> /==//
  { srw seq; apply Set.subset_union_of_subset_right=> ? /== ?
    exists i }
  apply hhlocal_subset s'=> //

private lemma lem_hsubst [Inhabited α] :
  z <= i ->
  i < n ->
  hhlocal s' H ->
  hsubst some (s' ∪ s) H = hsubst some (s' ∪ sᵢ i) H := by
  move=> * !h ! ⟨|⟩ ![h -> ? _] ⟨//|⟨|⟨//|?//⟩⟩⟩ <;> srw (lem_fsubst s z n (i := i)) //

@[simp]
lemma inj_some : Set.InjOn some s' = true := by move=> /== ? * //

set_option maxHeartbeats 1600000 in
lemma wp_for_bighop [Inhabited α] (β : Type)  [inst:Inhabited β]
  (Q : Int -> hval -> hhProp)
  (R R' : α -> hProp)
  (H₀ : hhProp)
  (Inv : Int -> hhProp)
  (Qgen : Int -> β -> hhProp)
  (ht : htrm) :
  z <= n ->
  hhlocal s' H₀ ->
  (∀ i, hhlocal s' (Inv i)) ->
  (∀ hv i, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (∀ x, x ∈ sᵢ j -> hv₁ x = hv₂ x) -> (Q j hv₁) = (Q j hv₂)) ->
  (∀ (hv : Int -> hval), ∀ j ∈ [[z,n]], ∃ v H, H₀ + ∑ i in [[z, j]], Q i (hv i) = Qgen j v ∗ H) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    Qgen j v ∗ Inv j ∗ (R ∗↑ (sᵢ j)) ==>
      LGTM.wp
           [⟨s', fun _ => subst vr j c⟩, ⟨sᵢ j, ht⟩]
           (fun hv' =>
             Q j hv' + Qgen j v ∗ Inv (j+1) ∗ R' ∗↑ sᵢ j)) ->
  H₀ ∗ Inv z ∗  R ∗↑ s ==>
    LGTM.wp
         [⟨s', fun _ => trm_for vr z n c⟩, ⟨s, ht⟩]
         (fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv n ∗ R' ∗↑ s) := by
  move=> L ???? eqQ gen *
  eapply wp_hsubst_some=> //'
  { simp=> ⟨|⟩ <;> apply hhlocal_subset s'=> //' }
  { move=> ?; srw hhProp_add_def /== => ⟨⟨|⟩|⟩
    { apply hhlocal_subset s'=> //' }
    { move=> *; apply hhlocal_subset s'=> //' }
    apply hhlocal_subset s'=> //' }
  srw hsubst_some_hhstar' //' ForLoopAux.LGTM.triple_Q_eq;  rotate_left
  {  move=> hv;
     rewrite [hhProp_add_def]
     rewrite [hsubst_some_hhstar']
     rewrite [<-hsubst_hhstar_same]
     rewrite [hsubst_hhstar_sum_same]
     rfl=> //'
     { move=> * [] //' }
     move=> * [] //' }
  srw Function.comp /=
  apply ForLoopAux.wp_for_bighop_aux _ _ _
    (fun i => ssubst some (s' ∪ s) $ sᵢ i) (ssubst some (s' ∪ s) s')
    (df := none)
    (Qgen := fun i v => hsubst some (s' ∪ s) (Qgen i v))
    (Inv := fun i => hsubst some (s' ∪ s) (Inv i))
    (inst := inst)
    (Q := fun j hv => hsubst some (s' ∪ s) (Q j (hv ∘ some)))=> //'
  { apply hhlocal_some=> //' }
  { move=> ?; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> ??; apply hhlocal_some=> //' }
  { move=> j hv₁ hv₂ ? hveq; congr! 1; apply eqQ=> //'
    move=> x ?; apply hveq=> //' /== ⟨|//'⟩; right; srw seq /==; exists j=> //' }
  { move=> > hj; scase!: (gen (hv · ∘ some) j hj)=> v H eq ⟨//|⟩
    exists hsubst some (s' ∪ s) H
    srw hsubst_hhstar_same //'
    { srw -eq ?hhProp_add_def -hsubst_hhstar_same //'
      { srw hsubst_hhstar_sum_same //' => * [] //' }
      move=> * [] //' }
    { shave/==: hhlocal s' (Qgen j v ∗ H)
      srw -eq ?hhProp_add_def //' }
    move=> * [] //' }
  { move=> > ?
    shave ?: Disjoint s' (sᵢ j)
    { move: seq disj=> ->; srw -disjoint_union=> /== // }
    srw (lem_s' s z n sᵢ) //' (lem_s s z n sᵢ) //'
    srw ?(lem_hsubst s z n sᵢ s' (i := j)) //' -hsubst_some_hhstar' //'
    srw LGTM.wp_Q_eq; rotate_left 2
    { move=> hv
      rewrite [hhProp_add_def, lem_hsubst s z n sᵢ s' (i := j)]
      rewrite [hsubst_hhstar_same]
      { srw -hsubst_some_hhstar' //' }
      all_goals auto
      move=> * [] //' }
    apply hsubst_wp=> //' /==
    { move=> * [] // }
    { constructor <;> apply hhlocal_subset s'=> //' }
    { move=> > hveq ?; congr; apply eqQ=> //' }
    move=> ?; rfl }
  { apply ssubst_some_disjoint=> // }
  srw [2]seq; clear *-L
  move: n; apply Int.le_induction
  { srw Finset.Ico_self /== => ! // }
  move=> n ? ih; srw sum_Ico_predr /== //' ssubst_some_union ih
  srw [2]sum_Ico_predr /== //

/- ------------------ [yfor] and [ywhile] tactics ------------------ -/

-- class SetIsBigUnion (shts : LGTM.SHTs α) (sᵢ : outParam (Int -> Set α)) where
--   eq : shts.set = ∑ i in [[z, n]], sᵢ i

-- instance {sᵢ' : Int -> Set α} :
--   SetIsBigUnion z n [⟨∑ i in [[z,n]], sᵢ' i, ht⟩] sᵢ' where
--   eq := by sdone


-- instance {sᵢ' : Int -> Set α} [h : SetIsBigUnion z n shts sᵢ] :
--   SetIsBigUnion z n
--     (⟨∑ i in [[z,n]], sᵢ' i, ht⟩ :: shts)List.Forall₂.length_eq
--     (fun i => sᵢ i ∪ sᵢ' i) where
--   eq := by
--     srw /== h.eq -set_plusE -Finset.sum_add_distrib
--     apply Finset.sum_congr=> // *; srw Set.union_comm //

class RestrictToIndex (shts:LGTM.SHTs α) (shtsᵢ : outParam (Int -> LGTM.SHTs α)) : Prop where
  sets_eq : ∀ (j : ℕ),
    j < shts.length ->
    shts[j]!.s = ∑ i in [[z,n]], (shtsᵢ i)[j]!.s
  ht_eq : ∀ i, z <= i ∧ i < n -> List.Forall₂ (fun s sᵢ => s.ht = sᵢ.ht) shts (shtsᵢ i)


instance : RestrictToIndex z n [⟨∑ i in [[z,n]], sᵢ i, ht⟩] (fun i => [⟨sᵢ i, ht⟩]) := by
  sdone

instance [r:RestrictToIndex z n shts shtsᵢ] :
   RestrictToIndex z n (⟨∑ i in [[z,n]], sᵢ i, ht⟩ :: shts) (fun i => (⟨sᵢ i, ht⟩ :: shtsᵢ i)) := by
  scase: r=> ??; constructor=> //== [] //

class IsGeneralisedSum (H₀ : hhProp) (Q : Int -> hval -> hhProp) (β : outParam Type) (Qgen : outParam (Int -> β -> hhProp)) where
  eq : ∀ (hv : Int -> hval), ∀ j ∈ [[z,n]], ∃ v H, H₀ + ∑ i in [[z, j]], Q i (hv i) = Qgen j v ∗ H

lemma shts_set_eq_sum (shts : LGTM.SHTs α) :
  shts.set = ∑ i in [[0, shts.length]], shts[i]!.s := by
  elim: shts=> //== sht shts ->; srw Finset.range_add_one' //

lemma RestrictToIndex.eq_length (restr: RestrictToIndex z n shts shtsᵢ) :
  ∀ i ∈ [[z,n]], shts.length = (shtsᵢ i).length := by
  move=> *;
  apply List.Forall₂.length_eq; apply restr.ht_eq=> //

lemma RestrictToIndex.set_eq
  (restr: RestrictToIndex z n shts shtsᵢ) :
  shts.set = ∑ i in [[z,n]], (shtsᵢ i).set := by
  srw shts_set_eq_sum (Finset.sum_congr rfl); rotate_left
  { move=> /== > /restr.sets_eq -> }
  srw Finset.sum_comm; apply (Finset.sum_congr rfl)=> *
  srw shts_set_eq_sum // restr.eq_length //;

lemma RestrictToIndex.cons_inv (restr: RestrictToIndex z n (sht :: shts) shtsᵢ') :
  ∃ (shtᵢ : Int -> LGTM.SHT) (shtsᵢ : Int -> LGTM.SHTs α),
   (∀ i ∈ [[z,n]], shtsᵢ' i = shtᵢ i :: shtsᵢ i) ∧
   sht.s = ∑ i in [[z,n]], (shtᵢ i).s ∧
   RestrictToIndex z n shts shtsᵢ ∧
   (∀ i ∈ [[z,n]], sht.ht = (shtᵢ i).ht)  := by
  exists (fun i => (shtsᵢ' i).head!), (fun i => (shtsᵢ' i).tail)
  scase: (restr)=> seq heq
  shave sE: ∀ i ∈ [[z, n]], shtsᵢ' i = List.head! (shtsᵢ' i) :: List.tail (shtsᵢ' i)
  { move=> > ?; srw List.cons_head!_tail -List.length_pos -restr.eq_length //' }
  repeat' constructor=> /= //';
  { move: (seq 0)=> /== ->; congr!; scase: (shtsᵢ' _)=> //== }
  { move=> j hj; move: (seq (j+1))=> /== -> //; apply Finset.sum_congr=> // i /== ??
    shave ?: j + 1 < (shtsᵢ' i).length
    { srw -restr.eq_length //== }
    srw ?getElem!_pos //== -List.drop_one -List.getElem_drop; congr! 2=> // }
  { move=> i /[dup] hi /heq; srw sE //' /== }
  move=> i /== ??
  specialize heq i ?_=> //; srw sE //' at heq; move: heq=> /== //




set_option maxHeartbeats 1600000 in
lemma RestrictToIndex.htrm_eq (restr: @RestrictToIndex α z n shts shtsᵢ)
  : shts.Pairwise (Disjoint ·.s ·.s) ->
    ∀ i ∈ [[z,n]], Set.EqOn (shtsᵢ i).htrm shts.htrm  (shtsᵢ i).set := by
    elim: shts shtsᵢ=> //==
    { move=>> [] /== eq ? /eq/[apply] -> // }
    move=> sht shts ih > /RestrictToIndex.cons_inv ![shtᵢ shtsᵢ] e /=->
    move=> /[dup] rstr /ih {}ih hteq dj₁ dj₂ i zi ni; srw e //' => a /== []
    { move=> ?; srw ?if_pos //' ?hteq //'
      exists i }
    move=> /[dup]?; srw shts_set_eq_sum /===> j ??
    shave h : j < shts.length
    { srw rstr.eq_length // }
    srw ?if_neg; { apply ih=> // }
    { simp=> k ??; move: (dj₁ shts[j]!);
      srw disjoint_comm -disjoint_union=> dj₁;
      apply Set.disjoint_left.mp
      { apply dj₁=> //'; srw List.mem_iff_getElem; exists j=> //'
        exists h=> //'; srw getElem!_pos // }
      srw rstr.sets_eq //' mem_union; exists i=> // }
    move: (dj₁ shts[j]!);
    srw disjoint_comm -disjoint_union=> dj₁;
    apply Set.disjoint_left.mp
    { apply dj₁=> //; srw List.mem_iff_getElem; exists j=> //
      exists h=> //; srw getElem!_pos // }
    srw rstr.sets_eq // mem_union; exists i=> //

lemma yfor_lemma
  [Inhabited α]
  [Inhabited β]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n H₀ Q β Qgen]
  (R R' : α -> hProp)
  (Inv : Int -> hhProp) :
  shts.Forall (Disjoint s' ·.s) ->
  shts.Pairwise (Disjoint ·.s ·.s) ->
  z <= n ->
  hhlocal s' H₀ ->
  (∀ i hv, hhlocal s' (Q i hv)) ->
  (∀ i, hhlocal s' (Inv i)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (shtsᵢ j).Forall (Set.EqOn hv₁ hv₂ ·.s) -> Q j hv₁ = Q j hv₂) ->
  (∀ i (v : β), z <= i ∧ i < n ->
    LGTM.triple
      (⟨s', fun _ => subst vr i c⟩ :: shtsᵢ i)
      (Qgen i v ∗ Inv i ∗ R ∗↑ (shtsᵢ i).set /- split with type classes? -/)
      (Q i · + Qgen i v ∗ Inv (i+1) ∗ R' ∗↑ (shtsᵢ i).set) /- split with type classes? -/) ->
  LGTM.triple (⟨s', fun _ => trm_for vr z n c⟩ :: shts)
    (H₀ ∗ Inv z ∗  R ∗↑ shts.set)
    (fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv n ∗ R' ∗↑ shts.set) := by
  move=> dj dj' ? ???? eqQ ind
  srw LGTM.triple LGTM.wp_squash_tail rstr.set_eq
  apply wp_for_bighop (Qgen := Qgen) (sᵢ := fun j => (shtsᵢ j).set)=> //'
  { move=>> ? hev; apply eqQ=> //'
    srw List.forall_iff_forall_mem=> ?; srw List.mem_iff_getElem
    scase! => i ? <- a ?; apply hev; srw shts_set_eq_sum mem_union
    exists i=> ⟨//|⟩; srw getElem!_pos // }
  { apply gen.eq }
  rotate_left
  { srw -rstr.set_eq; clear *-dj; clear rstr gen; elim: shts=> // }
  move=>> hj; move: (ind j v hj); srw LGTM.triple LGTM.wp_squash_tail
  srw ForLoopAux.wp2_ht_eq; { sapply }=> //'
  sby apply rstr.htrm_eq

lemma ywhile_lemma
  [Inhabited α]
  [Inhabited β]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n H₀ Q β Qgen]
  (R R' : α -> hProp)
  (Inv : Bool -> Int -> hhProp) :
  shts.Forall (Disjoint s' ·.s) ->
  shts.Pairwise (Disjoint ·.s ·.s) ->
  z <= n ->
  hhlocal s' H₀ ->
  (∀ i hv, hhlocal s' (Q i hv)) ->
  (∀ i b, hhlocal s' (Inv b i)) ->
  (∀ i b, hhlocal s' (Qgen i b)) ->
  (∀ j hv₁ hv₂, z <= j ∧ j < n -> (shtsᵢ j).Forall (Set.EqOn hv₁ hv₂ ·.s) -> Q j hv₁ = Q j hv₂) ->
  (∀ (i j : ℤ), (i != j) = true → z ≤ i ∧ i < n → z ≤ j ∧ j < n → Disjoint (shtsᵢ i).set (shtsᵢ j).set) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    LGTM.triple
        (⟨s', fun _ => c⟩:: shtsᵢ j)
        (Qgen j v ∗ (Inv true j) ∗ (R ∗↑ (shtsᵢ j).set))
        fun hv' =>
        Q j hv' + Qgen j v ∗ (∃ʰ b, (Inv b (j + 1))) ∗ R' ∗↑ (shtsᵢ j).set) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    LGTM.triple
        (shtsᵢ j)
        (Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (shtsᵢ j).set))
        fun hv' => Q j hv' + Qgen j v ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (shtsᵢ j).set)) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => ⌜(bv = fun _ => val.val_bool b)⌝ ∗ Inv b j)) ->
  (∀ b, Inv b n ==> ⌜b = false⌝ ∗ Inv b n) ->
    LGTM.triple
      (⟨s', fun _ => trm_while cnd c⟩ :: shts)
      (H₀ ∗ Inv b₀ z ∗ R ∗↑ shts.set)
      fun hv => H₀ + (∑ j in [[z, n]], Q j hv) ∗ Inv false n ∗ R' ∗↑ shts.set := by
  move=> dj ?????? eqQ dj' indt indf cndE cndN
  srw LGTM.triple LGTM.wp_squash_tail rstr.set_eq
  apply Disjoint.LGTM.wp_while_bighop (Qgen := Qgen)  (sᵢ := fun j => (shtsᵢ j).set)=> //'
  { move=>> ? hev; apply eqQ=> //'
    srw List.forall_iff_forall_mem=> ?; srw List.mem_iff_getElem
    scase! => i ? <- a ?; apply hev; srw shts_set_eq_sum mem_union
    exists i=> ⟨//|⟩; srw getElem!_pos // }
  { move=> ?; apply gen.eq }
  { srw -rstr.set_eq; clear *-dj; clear rstr gen; elim: shts=> // }
  { move=>> hj; move: (indt j v hj); srw LGTM.triple LGTM.wp_squash_tail
    srw ForLoopAux.wp2_ht_eq; { sapply }=> //'
    sby apply rstr.htrm_eq }
  move=>> hj; move: (indf j v hj)
  srw LGTM.triple ?LGTM.wp hwp_ht_eq /==; { sapply }=> //'
  move=> ??; srw rstr.htrm_eq //'
