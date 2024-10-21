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
import Mathlib.Data.Finset.Sups

import Lgtm.Common.Util
import Lgtm.Common.LabType
import Lgtm.Unary.SepLog
import Lgtm.Unary.WP1

import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.WP
import Lgtm.Hyper.Subst.Theory
import Lgtm.Hyper.Arrays

import Lgtm.Hyper.Loops.Theory

open Classical trm val prim
open SetSemiring

section

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

/- ------------------ [yfor] and [ywhile] tactics ------------------ -/

-- class SetIsBigUnion (shts : LGTM.SHTs α) (sᵢ : outParam (Int -> Set α)) where
--   eq : shts.set = ∑ i in ⟦z, n⟧, sᵢ i

-- instance {sᵢ' : Int -> Set α} :
--   SetIsBigUnion z n [⟨∑ i in ⟦z,n⟧, sᵢ' i, ht⟩] sᵢ' where
--   eq := by sdone


-- instance {sᵢ' : Int -> Set α} [h : SetIsBigUnion z n shts sᵢ] :
--   SetIsBigUnion z n
--     (⟨∑ i in ⟦z,n⟧, sᵢ' i, ht⟩ :: shts)List.Forall₂.length_eq
--     (fun i => sᵢ i ∪ sᵢ' i) where
--   eq := by
--     srw /== h.eq -set_plusE -Finset.sum_add_distrib
--     apply Finset.sum_congr=> // *; srw Set.union_comm //

class RestrictToIndex (z n) (shts:LGTM.SHTs α) (shtsᵢ : outParam (Int -> LGTM.SHTs α)) : Prop where
  sets_eq : ∀ (j : ℕ),
    j < shts.length ->
    shts[j]!.s = ∑ i in ⟦z,n⟧, (shtsᵢ i)[j]!.s
  ht_eq : ∀ i, z <= i ∧ i < n -> List.Forall₂ (fun s sᵢ => s.ht = sᵢ.ht) shts (shtsᵢ i)


instance RestrictToIndexNil (sᵢ : ℤ -> _) :
  RestrictToIndex z n [⟨∑ i in ⟦z,n⟧, sᵢ i, ht⟩] (fun i => [⟨sᵢ i, ht⟩]) := by
  sdone

lemma iUnion_eq_sum (f : Int -> Set α) :
  (⋃ i ∈ Set.Ico z n, f i) = (∑ i in Finset.Ico z n, f i)  := by sorry

lemma iUnion_eq_sum' (f : Int -> Set α) :
  (⋃ i ∈ Finset.Ico z n, f i) = (∑ i in Finset.Ico z n, f i)  := by sorry

instance RestrictToIndexNilU (sᵢ : ℤ -> _) :
  RestrictToIndex z n [⟨⋃ i ∈ (Set.Ico z n), sᵢ i, ht⟩] (fun i => [⟨sᵢ i, ht⟩]) := by
  srw iUnion_eq_sum
  sdone

instance RestrictToIndexCons (sᵢ : ℤ -> _) [r:RestrictToIndex z n shts shtsᵢ] :
   RestrictToIndex z n (⟨∑ i in ⟦z,n⟧, sᵢ i, ht⟩ :: shts) (fun i => (⟨sᵢ i, ht⟩ :: shtsᵢ i)) := by
  scase: r=> ??; constructor=> //== [] //

instance RestrictToIndexConsU (sᵢ : ℤ -> _) [r:RestrictToIndex z n shts shtsᵢ] :
   RestrictToIndex z n (⟨⋃ i ∈ Set.Ico z n, sᵢ i, ht⟩ :: shts) (fun i => (⟨sᵢ i, ht⟩ :: shtsᵢ i)) := by
  srw iUnion_eq_sum; exact inferInstance

-- instance RestrictToIndexConsUSet (sᵢ : ℤ -> _) [r:RestrictToIndex z n shts shtsᵢ] :
--    RestrictToIndex z n (⟨⋃ i ∈ Set.Ico z n, sᵢ i, ht⟩ :: shts) (fun i => (⟨sᵢ i, ht⟩ :: shtsᵢ i)) := by
--   apply RestrictToIndexConsU


class IsGeneralisedSum (z n) (add) (valid) [PartialCommMonoidWRT val add valid]
  (H₀ : hhProp) (Q : Int -> hval -> hhProp)
  (β : outParam Type)
  (Qgen : outParam (Int -> β -> hhProp))
  (Qind : outParam (Int -> β -> hval -> hhProp))
  (Qsum : outParam (hval -> hhProp)) where
  eqGen : ∀ (hv : Int -> hval), ∀ j ∈ ⟦z,n⟧, ∃ v H, H₀ + ∑ i in ⟦z, j⟧, Q i (hv i) = Qgen j v ∗ H
  eqInd : ∀ j hv v, Qind j v hv = Q j hv + Qgen j v
  eqSum : ∀ hv, Qsum hv = H₀ + ∑ i in ⟦z,n⟧, Q i hv


lemma shts_set_eq_sum (shts : LGTM.SHTs α) :
  shts.set = ∑ i in Finset.Ico 0 shts.length, shts[i]!.s := by
  elim: shts=> //== sht shts ->;srw Finset.range_add_one' //

lemma RestrictToIndex.eq_length (restr: RestrictToIndex z n shts shtsᵢ) :
  ∀ i ∈ ⟦z,n⟧, shts.length = (shtsᵢ i).length := by
  move=> *;
  apply List.Forall₂.length_eq; apply restr.ht_eq=> //

lemma RestrictToIndex.set_eq
  (restr: RestrictToIndex z n shts shtsᵢ) :
  shts.set = ∑ i in ⟦z,n⟧, (shtsᵢ i).set := by
  srw shts_set_eq_sum (Finset.sum_congr rfl); rotate_left
  { move=> /== > /restr.sets_eq -> }
  srw Finset.sum_comm; apply (Finset.sum_congr rfl)=> *
  srw shts_set_eq_sum // restr.eq_length //;

lemma RestrictToIndex.cons_inv (restr: RestrictToIndex z n (sht :: shts) shtsᵢ') :
  ∃ (shtᵢ : Int -> LGTM.SHT) (shtsᵢ : Int -> LGTM.SHTs α),
   (∀ i ∈ ⟦z,n⟧, shtsᵢ' i = shtᵢ i :: shtsᵢ i) ∧
   sht.s = ∑ i in ⟦z,n⟧ , (shtᵢ i).s ∧
   RestrictToIndex z n shts shtsᵢ ∧
   (∀ i ∈ ⟦z,n⟧, sht.ht = (shtᵢ i).ht)  := by
  exists (fun i => (shtsᵢ' i).head!), (fun i => (shtsᵢ' i).tail)
  scase: (restr)=> seq heq
  shave sE: ∀ i ∈ ⟦z, n⟧, shtsᵢ' i = List.head! (shtsᵢ' i) :: List.tail (shtsᵢ' i)
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
    ∀ i ∈ ⟦z,n⟧, Set.EqOn (shtsᵢ i).htrm shts.htrm  (shtsᵢ i).set := by
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
      srw disjoint_comm /== => dj₁;
      apply Set.disjoint_left.mp
      { apply dj₁=> //'; srw List.mem_iff_getElem; exists j=> //'
        exists h=> //'; srw getElem!_pos // }
      srw rstr.sets_eq //' mem_union; exists i=> // }
    move: (dj₁ shts[j]!);
    srw disjoint_comm /== => dj₁;
    apply Set.disjoint_left.mp
    { apply dj₁=> //; srw List.mem_iff_getElem; exists j=> //
      exists h=> //; srw getElem!_pos // }
    srw rstr.sets_eq // mem_union; exists i=> //

local notation (priority := high) Q " ∗↑ " s:70 => bighstar s Q

lemma yfor_lemma_aux'
  {c : htrm}
  [PartialCommMonoidWRT val add valid]
  [Inhabited α]
  [Inhabited β]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n add valid H₀ Q β Qgen Qind Qsum]
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
      (⟨s', fun j => subst vr i (c j)⟩ :: shtsᵢ i)
      (Qgen i v ∗ Inv i ∗ R ∗↑ (shtsᵢ i).set /- split with type classes? -/)
      (Qind i v · ∗ Inv (i+1) ∗ R' ∗↑ (shtsᵢ i).set) /- split with type classes? -/) ->
  Pre ==> H₀ ∗ Inv z ∗  R ∗↑ shts.set ->
  (fun hv => Qsum hv ∗ Inv n ∗ R' ∗↑ shts.set ) ===> Post ->
  LGTM.triple (⟨s', fun j => trm_for vr z n (c j)⟩ :: shts)
    Pre
    Post := by
  move=> dj dj' ? ???? eqQ ind preH postH
  apply LGTM.triple_conseq=> //'
  srw LGTM.triple LGTM.wp_squash_tail rstr.set_eq LGTM.wp_Q_eq; rotate_right
  { move=> ?; srw gen.eqSum }
  apply wp_for_bighop (Qgen := Qgen) (sᵢ := fun j => (shtsᵢ j).set)=> //'
  { move=>> ? hev; apply eqQ=> //'
    srw List.forall_iff_forall_mem=> ?; srw List.mem_iff_getElem
    scase! => i ? <- a ?; apply hev; srw shts_set_eq_sum mem_union
    exists i=> ⟨//|⟩; srw getElem!_pos // }
  { apply gen.eqGen }
  rotate_left
  { srw -rstr.set_eq; clear *-dj; clear rstr gen; elim: shts=> // }
  move=>> hj; srw LGTM.wp_Q_eq; rotate_right
  { srw -gen.eqInd //' }
  move: (ind j v hj); srw LGTM.triple LGTM.wp_squash_tail
  srw ForLoopAux.wp2_ht_eq; { sapply }=> //'
  sby apply rstr.htrm_eq

lemma ywhile_lemma
  [PartialCommMonoidWRT val add valid]
  [Inhabited α]
  [Inhabited β]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n add valid H₀ Q β Qgen Qind Qsum]
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
        Qind j v hv' ∗ (∃ʰ b, (Inv b (j + 1))) ∗ R' ∗↑ (shtsᵢ j).set) ->
  (∀ j (v : β), z <= j ∧ j < n ->
    LGTM.triple
        (shtsᵢ j)
        (Qgen j v ∗ (Inv false j) ∗ (R ∗↑ (shtsᵢ j).set))
        fun hv' => Qind j v hv' ∗ (Inv false (j + 1)) ∗ (R' ∗↑ (shtsᵢ j).set)) ->
  (∀ j b, z <= j ∧ j <= n ->
    htriple s' (fun _ => cnd) (Inv b j) (fun bv => ⌜(bv = fun _ => val.val_bool b)⌝ ∗ Inv b j)) ->
  (∀ b, Inv b n ==> ⌜b = false⌝ ∗ Inv b n) ->
    LGTM.triple
      (⟨s', fun _ => trm_while cnd c⟩ :: shts)
      (H₀ ∗ Inv b₀ z ∗ R ∗↑ shts.set)
      fun hv => Qsum hv ∗ Inv false n ∗ R' ∗↑ shts.set := by sorry

local notation (priority := high) "∗↓" Q => FindUniversal.univ Q

lemma hhlocal_hhlimpl :
  H₁ ==> H₀ → hhlocal s' H₀ → hhlocal s' H₁ := by
  sby move=> himpl hl ? /himpl /hl

lemma yfor_lemma_aux
  {c : htrm}
  [PartialCommMonoidWRT val add valid]
  [Inhabited α]
  [Inhabited β]
  [uPre : FindUniversal Pre Hu Pre']
  [uPost : forall hv, FindUniversal (Post hv) Hu' (Post' hv)]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n add valid H₀ Q β Qgen Qind Qsum]
  (R' : α -> hProp := fun _ => hempty)
  (R : α -> hProp := fun _ => hempty)
  (Inv : Int -> hhProp := fun _ => emp) :
  Hu ==> Hu' ->
  s'.Nonempty ->
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
      (⟨s', fun j => subst vr i (c j)⟩ :: shtsᵢ i)
      ((Qgen i v ∗ Inv i ∗ R ∗↑ (shtsᵢ i).set) ∗ Hu)
      ((Qind i v · ∗ Inv (i+1) ∗ R' ∗↑ (shtsᵢ i).set)  ∗ Hu)) ->
  Pre' ==> H₀ ∗ Inv z ∗  R ∗↑ shts.set ->
  (fun hv => Qsum hv ∗ Inv n ∗ R' ∗↑ shts.set ) ===> Post' ->
  LGTM.triple (⟨s', fun j => trm_for vr z n (c j)⟩ :: shts)
    Pre
    Post := by
  move=> HuImpl ? dj ??????? tr PreH PostH
  shave: Disjoint s' (∑ i ∈ ⟦z, n⟧, (shtsᵢ i).set)
  { srw -rstr.set_eq; clear *-dj; clear rstr gen; elim: shts=> // }
  move=> /== ?
  shave->: Post = Post' ∗ Hu'
  { move=> !hv
    rw [(uPost hv).H_eq]; ysimp; ysimp }
  apply LGTM.triple_conseq
  { apply hhimpl_refl }
  { move=> hv /=; apply hhimpl_frame_r; apply HuImpl }
  srw ?uPre.H_eq hhstar_comm uPre.Hu_eq
  apply LGTM.triple_conseq
  { apply hhimpl_frame_l; apply PreH }
  { move=> ? /=; apply hhimpl_frame_l; apply PostH }
  srw /=
  erw [LGTM.triple_extend_univ]=> //' /==
  { apply yfor_lemma_aux' (gen := gen)
     (R := fun a => R a ∗ ∗↓ Pre)
     (R' := fun a => R' a ∗ ∗↓ Pre)
     (Inv := fun i => Inv i ∗ [∗ in s'| ∗↓ Pre])=> //'
    { move=> > /[dup]? /(tr i v); srw uPre.Hu_eq LGTM.triple_extend_univ //' /==
      { apply LGTM.triple_conseq=> [|hv/=]
        { srw -?bighstar_hhstar -bighstar_hhstar_disj //'; ysimp }
        srw -?bighstar_hhstar -bighstar_hhstar_disj //'; ysimp }
      { move=> ⟨|⟩
        { apply hhlocal_subset; rotate_left=> //' }
        apply hhlocal_subset; rotate_left=> //'  }
      move=> ? /= ⟨|⟩
      { apply hhlocal_subset; rotate_left=> //';
        srw gen.eqInd //' }
      apply hhlocal_subset; rotate_left=> //' }
    { srw -bighstar_hhstar; ysimp
      srw -bighstar_hhstar_disj //';
      clear *-dj; clear rstr gen; elim: shts=> // }
    move=> ? /=; srw -bighstar_hhstar; ysimp
    srw -bighstar_hhstar_disj //'
    clear *-dj; clear rstr gen; elim: shts=> // }
  { move=> ⟨|⟩
    { apply hhlocal_subset; rotate_left=> //' }
    apply hhlocal_subset; rotate_left=> //' }
  move=> ? /= ⟨|⟩
  { apply hhlocal_subset; rotate_left=> //'
    srw gen.eqSum /==// }
  apply hhlocal_subset; rotate_left; auto
  auto

lemma zseq_lemma_aux (shts : LGTM.SHTs α) (ht₁ ht₂ : htrm) :
  Disjoint s shts.set ->
  LGTM.wp (⟨s, ht₁⟩ :: shts) (fun hv =>
    hwp s ht₂ (fun hv' => Q (hv' ∪_s hv) )) ==>
  LGTM.wp (⟨s, fun i => trm_seq (ht₁ i) (ht₂ i)⟩ :: shts) Q := by
  move=> ?
  srw [2]LGTM.wp_cons //=
  ychange hwp_seq=> /=
  srw LGTM.wp_cons //=; apply hwp_conseq=> hv /=
  -- simp [fun_insert]
  srw LGTM.wp_Q_eq; rotate_right
  { move=> ?; srw LGTM.hwp_Q_eq=> hv
    srw fun_insert_ss' }
  apply hhimpl_trans; apply LGTM.wp_cons_last (sht := ⟨s, _⟩)=> //
  srw LGTM.wp_cons=> //=

lemma zseq_lemma (H : hhProp) (shts : LGTM.SHTs α) (ht₁ ht₂ : htrm) :
  Disjoint s shts.set ->
  H ==> LGTM.wp (⟨s, ht₁⟩ :: shts) (fun hv =>
    hwp s ht₂ (fun hv' =>
      Q (hv' ∪_s hv) )) ->
  H ==>
    LGTM.wp (⟨s, fun i => trm_seq (ht₁ i) (ht₂ i)⟩ :: shts) Q := by
  move=> ??; ychange zseq_lemma_aux=> //

lemma yfor_lemma
  {c c' : htrm}
  {Post' : hval -> hhProp}
  [PartialCommMonoidWRT val add valid]
  [Inhabited α]
  [Inhabited β]
  [uPre : FindUniversal Pre Hu Pre']
  [uPost : forall hv, FindUniversal (Post hv) Hu' (Post' hv)]
  [rstr : RestrictToIndex z n shts shtsᵢ]
  [gen: IsGeneralisedSum z n add valid H₀ Q β Qgen Qind Qsum]
  (R' : α -> hProp := fun _ => hempty)
  (R : α -> hProp := fun _ => hempty)
  (Inv : Int -> hhProp := fun _ => emp) :
  Hu ==> Hu' ->
  s'.Nonempty ->
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
      (⟨s', fun j => subst vr i (c j)⟩ :: shtsᵢ i)
      ((Qgen i v ∗ Inv i ∗ R ∗↑ (shtsᵢ i).set) ∗ Hu)
      (fun hv => (Qind i v hv ∗ Inv (i+1) ∗ R' ∗↑ (shtsᵢ i).set)  ∗ Hu)) ->
  Pre' ==> H₀ ∗ Inv z ∗  R ∗↑ shts.set ->
  (∀ hv,
    Qsum hv ∗ Inv n ∗ R' ∗↑ shts.set ==> hwp s' c' (Post' $ · ∪_s' hv)) ->
  LGTM.triple (⟨s', fun j => trm_seq (trm_for vr z n (c j)) (c' j)⟩ :: shts)
    Pre
    Post := by
    move=> imp ? disj ????????? H
    apply zseq_lemma
    { srw shts_set_eq_sum /== => *
      move: disj; srw List.forall_iff_forall_mem; sapply
      srw getElem!_pos //'; apply List.getElem_mem }
    apply LGTM.triple_conseq
    { apply hhimpl_refl }
    { move=> hv /=; move: (H hv)
      move=> /(hhimpl_frame_lr) /(_ imp) /hhimpl_trans; sapply
      apply hhimpl_trans; apply hwp_frame; apply hwp_conseq=> hv /=
      rw [(uPost ..).H_eq, hhstar_comm]=>//' }
    shave un: ∀ hv, FindUniversal ((Qsum hv ∗ Inv n ∗ R' ∗↑ shts.set) ∗ Hu) Hu (Qsum hv ∗ Inv n ∗ R' ∗↑ shts.set)
    { move=> hv; apply FindUniversal.mk (univ := uPre.univ)=> //'
      { apply uPre.Hu_eq }
      srw hhstar_comm }
    apply yfor_lemma_aux (gen := gen) (Q := Q) (Inv := Inv) (Qgen := Qgen) (R := R) (R' := R')=> //';
