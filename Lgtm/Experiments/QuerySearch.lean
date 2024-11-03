import Mathlib.Data.Set.Card

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

def val.toNat : val -> Nat
  | val_int v => v.toNat
  | _ => 1

@[simp]
noncomputable def propToVal : Prop -> val := fun p => val_bool (decide p)

lemma val_bool_eq_propToVal :
  val_bool b = propToVal p ↔ b = p := by
  simp

noncomputable instance : Coe Prop val := ⟨propToVal⟩

@[simp]
lemma toBool_eq (b : Bool) : val.toBool b = b := by rfl

-- instance : Coe val Prop := ⟨fun v => v.toBool⟩

@[app_unexpander val.toBool] def unexpandToProp : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `($v)
  | _ => throw ( )

attribute [-simp] fun_insert Bool.forall_bool
attribute [simp] Set.univ_inter

theorem biUnion_prod_const (s': Set ι) {s : ι → Set α} {t : Set β} :
  (⋃ i ∈ s', s i) ×ˢ t = ⋃ i ∈ s', s i ×ˢ t := by
  ext
  simp=> ⟨|⟩ ![] // ![] //

lang_def Lang.getPoints :=
  fun pxind pyind i j =>
    let N := len pxind in
    let ind := Lang.find2Idx pxind pyind i j 0 N in
    ind != N

lang_def Lang.inBox :=
  fun xind yind boxl boxr =>
    let boxlx := boxl[0] in
    let boxly := boxl[1] in
    let boxrx := boxr[0] in
    let boxry := boxr[1] in

    let xinl := boxlx <= xind in
    let xinr := xind < boxrx in
    let xin := xinl && xinr in

    let yinl := boxly <= yind in
    let yinr := yind < boxry in
    let yin := yinl && yinr in

    xin && yin

lang_def Lang.getBox := fun boxl boxr i j => Lang.inBox i j boxl boxr


lang_def Lang.beforeBox :=
  fun xind yind boxl boxr =>
    let boxrx := boxr[0] in
    let boxry := boxr[1] in

    let xinr := xind < boxrx in
    let yinr := yind < boxry in

    xinr && yine


lang_def Lang.boxCountQuery :=
  fun pxind pyind boxl boxr  =>
    ref ans := 0 in
    let N := len pxind in
    for i in [0:N] {
      let xind := pxind[i] in
      let yind := pyind[i] in
      let InBox := Lang.inBox xind yind boxl boxr in
      if InBox then
        incr ans
      else ()
    }; !ans

namespace BoxCount
variable (xind yind boxl boxr : loc) (N : ℕ)
variable (x_ind : ℤ -> ℝ) (y_ind : ℤ -> ℝ) (box_l box_r : ℤ -> ℝ)

#hint_yapp triple_hharrayFun_get
#hint_yapp triple_hharrayFun_length
#hint_yapp htriple_eq
#hint_yapp htriple_neq
#hint_yapp htriple_get
-- #hint_yapp htriple_free
#hint_yapp htriple_sub
#hint_yapp htriple_ler
#hint_yapp htriple_ltr
#hint_yapp htriple_add
#hint_yapp htriple_ptr_add



variable (xy_ind_uniq : Set.InjOn (fun i => (x_ind i, y_ind i)) ⟦0, N⟧)
include xy_ind_uniq

lemma get_spec_out (l : ℕ) (s : Set (ℝ × ℝ)) :
  (∀ᵉ (i ∈ s) (j ∈ ⟦0,N⟧), ¬ (x_ind j = i.1 ∧ y_ind j = i.2)) ->
  arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,s⟫⟩(yind, x in N => y_ind x) ==>
    WP [l| ij in s => Lang.getPoints xind yind ⟨ij.val.1⟩ ⟨ij.val.2⟩] { v,
     ⌜ v = fun _ => val_bool false ⌝ ∗
     arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
     arr⟨⟪l,s⟫⟩(yind, x in N => y_ind x) } := by
  move=> nin
  ystep; ywp; yapp Lang.find2Idx_hspec_out
  { yapp; ysimp }
  move=> ??; apply nin=> //

notation "·" => (Set.univ)

def toProp : val -> Prop
  | val_bool v => v
  | _ => False

instance : Coe val Prop := ⟨(·.toBool = true)⟩

-- @[app_unexpander toProp] def unexpandToProp : Lean.PrettyPrinter.Unexpander
--   | `($_ $v) => `($v)
--   | _ => throw ( )

attribute [-simp] hhwandE
lemma get_spec_in (l : ℕ) (k : ℤ) :
  0 <= k ∧ k < N ->
  arr⟨⟪l,{(x_ind k, y_ind k)}⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,{(x_ind k, y_ind k)}⟫⟩(yind, x in N => y_ind x) ==>
    WP [l| ij in {(x_ind k, y_ind k)} => Lang.getPoints xind yind ⟨ij.val.1⟩ ⟨ij.val.2⟩] { v,
     ⌜ v = fun _ => val_bool true ⌝ ∗
    arr⟨⟪l,{(x_ind k, y_ind k)}⟫⟩(xind, x in N => x_ind x) ∗
    arr⟨⟪l,{(x_ind k, y_ind k)}⟫⟩(yind, x in N => y_ind x) } := by
  move=> ?
  ystep; simpWP; ywp; yapp Lang.find2Idx_hspec
  yapp; ysimp=> /== //'; funext=> /== //'

set_option maxRecDepth 1500
set_option maxHeartbeats 3200000

def InBox x y := (box_l 0 <= x ∧ x < box_r 0) ∧ (box_l 1 <= y ∧ y < box_r 1)

omit xy_ind_uniq in
@[yapp]
lemma inBox_spec' (f₁ f₂ : (ℝ×ℝ)ˡ -> ℝ) :
  arr⟨⋆⟩(boxl, x in 2 => box_l x) ∗
  arr⟨⋆⟩(boxr, x in 2 => box_r x) ==>
  hwp ⟪l, r⟫ (fun ij => [lang| Lang.inBox ⟨f₁ ij⟩ ⟨f₂ ij⟩ boxl boxr]) fun v =>
    ⌜ v = fun ij => propToVal (InBox box_l box_r (f₁ ij) (f₂ ij)) ⌝ ∗
    arr⟨⋆⟩(boxl, x in 2 => box_l x) ∗
    arr⟨⋆⟩(boxr, x in 2 => box_r x) := by
  sdo 10 (ystep=> //'); yapp; ysimp=> /==
  funext ⟨i, j⟩; simp [InBox]

omit xy_ind_uniq in
lemma inBox_spec (i j : ℝ) :
  { arr⟨⋆⟩(boxl, x in 2 => box_l x) ∗
    arr⟨⋆⟩(boxr, x in 2 => box_r x) }
  [1| x in {r} => Lang.inBox i j boxl boxr]
  [2| ij in @Set.univ (ℝ × ℝ) => Lang.getBox boxl boxr ⟨ij.val.1⟩ ⟨ij.val.2⟩]
  {v,
    ⌜ v ⟨1,r⟩ = ((i, j) ∈ {ij | v ⟨2, ij⟩ }) ⌝ ∗
    arr⟨⋆⟩(boxl, x in 2 => box_l x) ∗
    arr⟨⋆⟩(boxr, x in 2 => box_r x) } := by
  yin 1: yapp
  ystep; ysimp



lemma boxSerachQuery_spec :
  { arr⟨⋆⟩(boxl, x in 2 => box_l x) ∗
    arr⟨⋆⟩(boxr, x in 2 => box_r x) ∗
    arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(yind, x in N => y_ind x) }
  [1| x in {r} => Lang.boxCountQuery xind yind boxl boxr]
  [2| ij in @Set.univ (ℝ × ℝ) => Lang.getPoints xind yind ⟨ij.val.1⟩ ⟨ij.val.2⟩]
  [3| ij in @Set.univ (ℝ × ℝ) => Lang.getBox boxl boxr ⟨ij.val.1⟩ ⟨ij.val.2⟩]
  {v,
    ⌜ (v ⟨1,r⟩).toNat = ({ij | v ⟨2, ij⟩ } ∩ {ij | v ⟨3, ij⟩ }).encard ⌝  ∗ ⊤ } := by stop
  yin 3: ystep
  yfocus 2, (fun i => (x_ind i, y_ind i)) '' ⟦0, N⟧
  yapp get_spec_out=> /==; simp [fun_insert]
  yin 1: ywp; yref p; ystep
  srw [1]Set.image_eq_iUnion
  yfor+ with
    (Q := fun i hv => p ~⟪1, {r}⟫~> val_int (if InBox box_l box_r (x_ind i) (y_ind i) then 1 else 0) ∗ ⌜hv ⟨2, x_ind i, y_ind i⟩⌝ )
    (H₀ := p ~⟪1, {r}⟫~> 0);
  { move=> > ??
    yin 1: ystep=> //'; ystep=> //'; ystep; ywp; yif=> /== cnd
    { yin 1: yapp
      yapp get_spec_in; ysimp; srw if_pos // }
    yin 1: ywp; yval
    yapp get_spec_in; ysimp }
  { sdone }
  yapp=> hvIn; ysimp=> /==
  erw [<-Finset.sum_image (g := fun i => (x_ind i, y_ind i)) (f := fun i => if InBox _ _ i.1 i.2 then 1 else 0)]
  erw [Finset.sum_ite, Finset.sum_const_zero]; simp [-Finset.mem_Ico, toNat]=> //'
  srw -Set.ncard_coe_Finset Set.Finite.cast_ncard_eq
  { congr! => ! [r₁ r₂] /== ? ⟨xin|⟩
    { srw if_pos //; move: xin=> /== ??? <-<- //' }
    scase_if=> // }
  apply Finset.finite_toSet

end BoxCount

namespace IntervalCount
set_option maxRecDepth 1500
set_option maxHeartbeats 3200000

-- open AddPCM in
-- lemma arr_eq_sum (m : ℕ) (op : β -> ℤ)  (f : β -> ℤ) (fs : Finset β):
--   f '' fs ⊆ Set.Ico 0 m →
--   hharrayFun s (fun i => val_int 0) m x + (∑ i ∈ fs, (x j + 1 + (f i).natAbs ~⟨j in s⟩~> op i)) =
--   hharrayFun s (fun id => val_int (∑ i in { x ∈ fs | f x = id }, op i)) m x := by sorry

private lemma boo (n : ℕ) :
  (∀ i ∈ ⟦0, n⟧, f i = g i) ->
  hharrayFun s f n p ==> hharrayFun s g n p := by sorry

@[app_unexpander hharrayFun]
def hharrayFunUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $f $n fun $_ => $p) =>
    match s with
    | `(Set.univ) => `(⋯)
    | `(⋆) => `(⋯)
    | _ =>
      match f with
      | `(fun $x:ident => $f) =>
        `(arr($p ⟨$s:term⟩ , $x:ident in $n => $f))
      | _ => throw ( )
  | _ => throw ( )

lang_def Lang.inInt :=
  fun i intl intr =>
    let iLl := intl <= i in
    let iLr := i < intr in
    iLl && iLr

-- lang_def Lang.intervalCountQuery :=
--   fun xind xid intl intr out =>
--     let N := len xind in
--     for i in [0:N] {
--       let ind := xind[i] in
--       let id  := xid[i] in
--       let InInt := Lang.inInt ind intl intr in
--       if InInt then
--         let out' := out ++ 1 in
--         let out' := out' ++ id in
--         Lang.incr out'
--       else ()
--     }; ()

lang_def Lang.intervalCountQuery' :=
  fun xind xid intl intr out z n =>
    let N := len xind in
    ref cnt := z in
    while (
      let i := !cnt in
      let inBounds := i < n in
      if inBounds then
        let ind := xind[i] in
        ind < intr
      else false) {
      let i := !cnt in
      let ind := xind[i] in
      let indLr := intl <= ind in
      if indLr then
        let id := xid[i] in
        let out' := out ++ 1 in
        let out' := out' ++ id in
        Lang.incr out';
        Lang.incr cnt
      else Lang.incr cnt
    }

lang_def Lang.mem :=
  fun xind xid i id z n =>
    let N := len xind in
    let n' := Lang.find2Idx xind xid i id z n in
    n' != n

variable (xind xid : loc) (z n : ℤ) (N : ℕ) (M : ℕ)
variable (x_ind : ℤ -> ℝ) (x_id : ℤ -> ℤ) (intl intr : ℝ) (out : loc)
variable (intl intr : ℝ)
variable (x_id_range : x_id '' ⟦z, n⟧ ⊆ Set.Ico 0 M)
variable (zLn : z <= n) (oLz : 0 <= z) (nLN : n <= N)

section
variable (x_ind_inj : Set.InjOn x_ind ⟦z, n⟧)

include x_ind_inj zLn oLz nLN

lemma mem_spec_out (l : ℕ) (s : Set (ℝ × ℤ)) :
  (∀ᵉ (i ∈ s) (j ∈ ⟦z,n⟧), ¬ (x_ind j = i.1 ∧ x_id j = i.2)) ->
  arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,s⟫⟩(xid, x in N => x_id x) ==>
    WP [l| ij in s => Lang.mem xind xid ⟨ij.val.1⟩ ⟨ij.val.2⟩ z n] { v,
     ⌜ v = fun _ => val_bool false ⌝ ∗
     arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
     arr⟨⟪l,s⟫⟩(xid, x in N => x_id x) } := by
  move=> nin
  ystep; ywp; yapp Lang.find2Idx_hspec_out'
  { yapp; ysimp }
  move=> ??;
  { move=> ?? /= /== /x_ind_inj // }
  apply nin=> //


attribute [-simp] hhwandE
lemma mem_spec_in (l : ℕ) (k : ℤ) :
  z <= k ∧ k < n ->
  arr⟨⟪l,{(x_ind k, x_id k)}⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,{(x_ind k, x_id k)}⟫⟩(xid, x in N => x_id x) ==>
    WP [l| ij in {(x_ind k, x_id k)} => Lang.mem xind xid ⟨ij.val.1⟩ ⟨ij.val.2⟩ z n] { v,
     ⌜ v = fun _ => val_bool true ⌝ ∗
    arr⟨⟪l,{(x_ind k, x_id k)}⟫⟩(xind, x in N => x_ind x) ∗
    arr⟨⟪l,{(x_ind k, x_id k)}⟫⟩(xid, x in N => x_id x) } := by
  move=> ?
  ystep; simpWP; ywp; yapp Lang.find2Idx_hspec'
  { yapp; ysimp=> /== //'; funext=> /== //' }
  move=> ???? /= /== /x_ind_inj //

lemma mem_spec_term (l : ℕ) (s : Set α) (x : αˡ -> ℝ) (y : αˡ -> ℤ) :
  -- (∀ᵉ (i ∈ s) (j ∈ ⟦z,n⟧), ¬ (x_ind j = i.1 ∧ x_id j = i.2)) ->
  arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
  arr⟨⟪l,s⟫⟩(xid, x in N => x_id x) ==>
    WP [l| ij in s => Lang.mem xind xid ⟨x ij⟩ ⟨y ij⟩ z n] { v,
     arr⟨⟪l,s⟫⟩(xind, x in N => x_ind x) ∗
     arr⟨⟪l,s⟫⟩(xid, x in N => x_id x) } := by sorry
  -- move=> nin
  -- ystep; ywp; yapp Lang.find2Idx_hspec_out'
  -- { yapp; ysimp }
  -- move=> ??;
  -- { move=> ?? /= /== /x_ind_inj // }
  -- apply nin=> //

omit x_ind_inj in
@[yapp]
lemma mem_inte_in (i : ℝ) :
  emp ==>
    WP [l| ij in s => Lang.inInt i intl intr ] { v,
     ⌜ v = fun _ => propToVal (i ∈ Set.Ico intl intr) ⌝ } := by
  ystep; ystep; yapp

include x_id_range

-- lemma intervalCountQuery_spec :
--   { arr⟨⋆⟩(xind, x in N => x_ind x) ∗
--     arr⟨⋆⟩(xid,  x in N => x_id x) ∗
--     arr⟨⟪1, {r}⟫⟩(out,  x in M => val_int 0) }
--   [1| x in {r} => Lang.intervalCountQuery xind xid intl intr out]
--   [2| ij in @Set.univ (ℝ × ℤ) => Lang.mem xind xid ⟨ij.val.1⟩ ⟨ij.val.2⟩]
--   {v,
--     arr⟨⟪1, {r}⟫⟩(out, id in M => val_int ({i | v ⟨2,i,id⟩} ∩ Set.Ico intl intr).ncard)  ∗ ⊤ } := by
--   yfocus 2, (fun i => (x_ind i, x_id i)) '' ⟦0, N⟧
--   yapp mem_spec_out=> /==; simp [fun_insert]
--   yin 1: ystep
--   srw [1]Set.image_eq_iUnion
--   let op (hv : hval (ℝ×ℤ)ˡ) i := if hv ⟨2, x_ind i, x_id i⟩ ∧ intl <= x_ind i ∧ x_ind i < intr then (1 : ℤ) else 0
--   yfor+ with
--     (Q := fun j hv => out + 1 + (x_id j).natAbs ~⟪1, {r}⟫~> op hv j)
--     (H₀ := arr⟨⟪1, {r}⟫⟩(out,  x in M => val_int 0) ∗ ⌜x_id '' ⟦0, N⟧ ⊆  Set.Ico 0 M⌝) <;> try simp [op]
--   { move=> > ?? -> // }
--   { move=> > ??
--     shave ?: x_id i >= 0
--     { simp: (@x_id_range (x_id i))=> /(_ i); omega }
--     yin 2: yapp mem_spec_in
--     simp; (sdo 3 ystep=> //'); ywp; yif=> [/== ??|/== cnd]
--     { ystep=> //' /==; ystep=> //'
--       shave->: ((((Nat.cast out) + 1) : ℤ).natAbs + x_id i).natAbs = out + 1 + (x_id i).natAbs;
--       { move: out; unfold loc; omega }
--       yapp; ysimp; srw if_pos //' }
--     ywp; yval; ysimp }
--   { ysimp=> // }
--   ysimp=> _; ywp; yval
--   open AddPCM in erw [<-Finset.sum_image
--        (g := fun i => (x_ind i, x_id i))
--        (f := fun i => _ + i.2.natAbs ~⟪1, _⟫~> val_int (if (hv ⟨2, i⟩).toBool = _ ∧ _ ≤ i.1 ∧ i.1 < _ then 1 else 0))]
--   { open AddPCM in srw arr_eq_sum=> //'
--     { apply boo=> /== i ??; srw -Set.ncard_coe_Finset /==
--       apply Set.ncard_congr (f := fun x _ => x.1)=> /== //'
--       { move=> > ?? <- <- <-; srw if_pos //'; exists x=> //' }
--       move=> >; scase_if=> /== > ?? <- <- ???; exists (x_id x)=> ⟨⟨|//'⟩|//'⟩
--       exists x=> //' }
--     move=> i /==; move: (@x_id_range i)=> /== //' }
--   move=> ? /x_ind_inj /== H ??? /H //'

end

variable (x_ind_inj : StrictMonoOn x_ind ⟦z, n⟧)
include x_ind_inj x_id_range zLn oLz nLN

lemma intervalCountQuery'_spec (ini : ℤ -> ℤ) :
  { arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xid,  x in N => x_id x) ∗
    arr⟨⟪1, {r}⟫⟩(out,  x in M => ini x) }
  [1| x in {r} => Lang.intervalCountQuery' xind xid intl intr out z n]
  [2| ij in @Set.univ (ℝ × ℤ) => Lang.mem xind xid ⟨ij.val.1⟩ ⟨ij.val.2⟩ z n]
  {v,
    ⌜∀ id ∈ ⟦0,M⟧, ({i | v ⟨2,i,id⟩} ∩ Set.Ico intl intr).Finite⌝ ∗
    arr⟨⟪1, {r}⟫⟩(out, id in M => val_int $ ini id + ({i | v ⟨2,i,id⟩} ∩ Set.Ico intl intr).ncard) ∗
    arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xid,  x in N => x_id x) } := by
  shave Inj: Set.InjOn x_ind (Set.Ico z n)
  { apply StrictMonoOn.injOn
    move=>  /== ??? ??? /x_ind_inj; sapply=> /== //' }
  yfocus 2, (fun i => (x_ind i, x_id i)) '' ⟦z, n⟧
  yapp mem_spec_out=> /==; simp [fun_insert]
  yin 1: ystep=> //'; ywp; yref ind
  srw [1]Set.image_eq_iUnion
  let op (hv : hval (ℝ×ℤ)ˡ) i := if hv ⟨2, x_ind i, x_id i⟩ ∧ intl <= x_ind i ∧ x_ind i < intr then (1 : ℤ) else 0
  let cond (i : ℤ) := i < n ∧ x_ind i < intr
  ywhile+ z, n with (b₀ := cond z)
    (Inv := fun b i => (if i < n ∧ x_ind i < intr then ind ~⟪1, {r}⟫~> i else ∃ʰ (j : ℤ), (ind ~⟪1, {r}⟫~> j) ∗ ⌜z <= j ∧ (j < n -> intr <= x_ind (j))⌝) ∗ ⌜0 <= i ∧ i <= n ∧ cond i = b⌝ )
    (Q := fun j hv => out + 1 + (x_id j).natAbs ~⟪1, {r}⟫~> op hv j)
    (H₀ := arr⟨⟪1, {r}⟫⟩(out,  x in M => ini x) ∗ ⌜x_id '' ⟦z, n⟧ ⊆  Set.Ico 0 M⌝) <;> try simp [op]
  { move=> ?; scase_if; simp [hhlocalE]; srw hhlocal_hhexists; simp [hhlocalE] }
  { move=> > ?? -> // }
  { move=> > ??
    shave ?: x_id j >= 0
    { simp: (@x_id_range (x_id j))=> /(_ j); omega }
    yin 2: yapp mem_spec_in=> /== _ _ _ ?
    srw if_pos //'
    simp; sdo 3 ystep
    ywp; yif=> /== ?
    { srw if_pos //'; ystep=> //'; ystep=> //' /==; ystep=> //'
      shave->: ((((Nat.cast out) + 1) : ℤ).natAbs + x_id j).natAbs = out + 1 + (x_id j).natAbs;
      { move: out; unfold loc; omega }
      ystep; yapp; ysimp[decide (cond (j + 1))]=> /== //'
      scase_if=> /== * <;> ysimp; move=> ⟨|⟩ //' }
    yapp; ysimp[decide (cond (j + 1))]=> /== //'
    scase_if=> /== * <;> ysimp; move=> ⟨|⟩ //' }
  { move=> > ? jN; srw LGTM.triple ywp1
    yapp mem_spec_in=> /== _ _; srw cond /== => /(_ (jN)) Le
    shave ?: j + 1 < n → intr ≤ x_ind (j + 1); { move=> ?; apply le_trans Le; apply le_of_lt; apply x_ind_inj=> /== //' }
    srw ?if_neg /== //'
    ypull=> i ?; ysimp=> //' ⟨|⟨|?⟩⟩ //' }
  { move=> > ??; scase_if=> L
    { ystep=> /== ??; srw cond=> ?; ywp; yapp htriple_lt
      ywp; yif=> /== ?
      { ystep; yapp; ysimp=> //'
        funext=> /==; scase: b=> /== // }
      ywp; yval; ysimp=> //' }
    srw -hwp_equiv; ypull=> i=> /== ??; srw cond=> ?; ystep; ywp; yapp htriple_lt
    ywp; yif=> /== ?
    { ystep; yapp; ysimp=> //'
      funext=> /==; scase: b=> /== * //' }
    simp at L
    ywp; yval; ysimp=> //'; funext; scase: b=> /== //' }
  { move=> ?; srw cond /==; ysimp=> //' }
  { ysimp=> //; scase_if=> /== ?; ysimp=> //' ⟨|⟩ //' }
  open AddPCM in erw [<-Finset.sum_image
    (g := fun i => (x_ind i, x_id i))
    (f := fun i => _ + i.2.natAbs ~⟪1, _⟫~> val_int (if (v ⟨2, i⟩).toBool = _ ∧ _ ≤ i.1 ∧ i.1 < _ then 1 else 0))]
  rotate_left
  { move=> ?? ?? /== /Inj /[swap] ?; sapply=> // }
  open AddPCM in srw arr_eq_sum=> //'; rotate_left
  { move=> i /==; move: (@x_id_range i)=> /== //' }
  ypull=> _ j ??; ysimp[Flase]
  { move=> /== i ??; srw -Set.ncard_coe_Finset /==
    apply Set.ncard_congr (f := fun x _ => x.1)=> /== //'
    { move=> > ?? <- <- <-; srw if_pos //'; exists x=> //' }
    move=> >; scase_if=> /== > ?? <- <- ???; exists (x_id x)=> ⟨⟨|//'⟩|//'⟩
    exists x=> //' }
  { move=> id > ??
    srw (Equiv.set_finite_iff (t :=
        (Finset.filter (fun x ↦ (v ⟨2, x⟩).toBool = true ∧ intl ≤ x.1 ∧ x.1 < intr)
         (Finset.filter (fun x ↦ x.2 = id) (Finset.image (fun i ↦ (x_ind i, x_id i)) (Finset.Ico z n)))).toSet))=> //'
    apply Finset.finite_toSet
    apply Equiv.mk
      (toFun := fun ⟨x, pf⟩ => ⟨(x,id),
        by simp: pf; scase_if=> /== > ?? <- <- ??? ⟨|⟩//'⟩)
      (invFun := fun ⟨⟨x, id⟩ , pf⟩ => ⟨x,
        by simp: pf=> > ?? <- <- <-; srw if_pos //'; exists x=> //'⟩)
    { move=> ? /== }
    move=> /== // }
  ysimp[]

end IntervalCount

open IntervalCount

lang_def Lang.boxCountQuery' :=
  fun yprt yind xind xid ybox xbox out =>
    let N := len yind in
    ref cnt := 0 in
    while (
      let i := !cnt in
      let inBounds := i < N in
      if inBounds then
        let ind := yind[i] in
        let intr := ybox[1] in
        ind < intr
      else false) {
      let i := !cnt in
      let ind := yind[i] in
      let intl := ybox[0] in
      let indLr := intl <= ind in
      if indLr then
        let z := yprt[i] in
        let i' := i + 1 in
        let n := yprt[i'] in
        let intl := xbox[0] in
        let intr := xbox[1] in
        Lang.intervalCountQuery' xind xid intl intr out z n;
        Lang.incr cnt
      else Lang.incr cnt
    }

lang_def Lang.mem2 :=
  fun yprt yind xind xid i j id =>
    let N := len yind in
    let n := Lang.findIdx yind i 0 N in
    let inBounds := n != N in
    if inBounds then
      let z := yprt[n] in
      let i' := n + 1 in
      let n := yprt[i'] in
      Lang.mem xind xid j id z n
    else false


variable (yind xind xid yptr ybox xbox : loc) (N : ℕ) (M : ℕ) (K : ℕ)
variable (x_ind y_ind : ℤ -> ℝ) (x_id : ℤ -> ℤ) (y_ptr : ℤ -> ℤ) (x_box y_box : ℤ -> ℝ) (out : loc)
variable (x_id_range : x_id '' ⟦0, N⟧ ⊆ Set.Ico 0 K)
variable (y_prt_mon : MonotoneOn y_ptr ⟦0, M+1⟧)
variable (y_ptr0 : y_ptr 0 = 0)
variable (y_ptrM : y_ptr M = N)
variable (y_ind_mono : StrictMonoOn y_ind ⟦0, M⟧)
variable (x_ind_mon : ∀ i ∈ ⟦0, M⟧, StrictMonoOn x_ind ⟦y_ptr i, y_ptr (i + 1)⟧)

def Box := { (i, j) | x_box 0 <= i ∧ i < x_box 1 ∧ y_box 0 <= j ∧ j < y_box 1 }

include y_ind_mono

set_option maxHeartbeats 1600000 in
lemma mem2_spec_out (s : Set (ℝ × ℝ × ℤ)) :
  Disjoint s ((y_ind '' ⟦0, M⟧) ×ˢ ⋆) ->
  arr⟨⟪l,s⟫⟩(yind , x in M => y_ind x)  ==>
  WP [l| ijk in s => Lang.mem2 yptr yind xind xid ⟨ijk.val.1⟩ ⟨ijk.val.2.1⟩ ⟨ijk.val.2.2⟩] { v,
    ⌜v = fun _ => val_bool false⌝ ∗
    arr⟨⟪l,s⟫⟩(yind , x in M => y_ind x)  } := by stop
    move=> /Set.disjoint_left dj; ystep
    ywp; yapp Lang.findIdx_hspec_out=> //'
    { ystep; ywp; yifF=> //'; ywp; yval; ysimp=> //' }
    { sby apply StrictMonoOn.injOn }
    scase=> /== ? > ? /dj /==

set_option maxRecDepth 2000
set_option maxHeartbeats 6400000

attribute [-simp] Set.singleton_prod

include x_id_range y_ptr0 y_ptrM y_prt_mon
omit y_ind_mono in
lemma y_prt_range_j :
  j ∈ ⟦0, M⟧ ->
  x_id '' ↑(Finset.Ico (y_ptr j) (y_ptr (j + 1))) ⊆ Set.Ico 0 K := by
  simp only [Finset.mem_Ico, Finset.coe_Ico, and_imp]
  move=> ??; apply subset_trans; rotate_left=> //
  apply Set.image_mono=> ? /== ?? ⟨|⟩
  { apply le_trans'=> //; srw -y_ptr0
    apply y_prt_mon=> /== //' }
  apply Int.lt_of_lt_of_le=> //;
  apply le_trans (b := y_ptr (M ))=> //
  apply y_prt_mon=> /== //'

include x_ind_mon

omit x_id_range y_prt_mon y_ptr0 y_ptrM y_ind_mono x_ind_mon in
private lemma proj_box (v : hval (ℝ×ℤ)ˡ) :
    0 ≤ i →
    i < K →
    y_ind j < y_box 1 ->
    y_box 0 ≤ y_ind j ->
      ({i_1 | (v ⟨2, (i_1, i)⟩).toBool = true} ∩ Set.Ico (x_box 0) (x_box 1)).ncard =
        ({y_ind j} ×ˢ {i_1 | (v ⟨2, (i_1, i)⟩).toBool = true} ∩ Box y_box x_box).ncard := by
  move=> > ?? ??; apply Set.ncard_congr (f := fun x _ => (y_ind j, x))=> /== //'
  move=> > ->; simp [Box]=> -> //

open Classical

lemma f (r : ℝ × ℝ × ℤ) (v : ℤ -> ℤ) (x x_1 : hval (ℝ×ℤ)ˡ) (j : ℤ) (cond := fun (i : ℤ) => i < N ∧ y_ind i < y_box 1) :
  0 ≤ j →
  j < M →
  -- y_ind j < y_box 1 →
  y_box 0 > y_ind j →
  arr⟨⋆⟩(xind, x in N => x_ind x) ∗
  arr⟨⋆⟩(xid,  x in N => x_id x) ∗
  ind ~⟨i in ⟪1, {r}⟫⟩~> j ∗ arr⟨⟪1, {r}⟫⟩(out, x in K => val_int (v x)) ==>
  (NWP [1| a in {r} => Lang.incr ind]
    [2| a in {y_ind j} ×ˢ ⋆ => Lang.mem xind xid ⟨a.val.2.1⟩ ⟨a.val.2.2⟩ ⟨y_ptr j⟩ ⟨y_ptr (j + 1)⟩]
    { x,
      arr⟨⟪1, {r}⟫⟩(out, j_1 in K =>
            val_int (v j_1 + ↑({y_ind j} ×ˢ {j_2 | (x ⟨2, (y_ind j, j_2, j_1)⟩).toBool = true} ∩ Box y_box x_box).ncard)) ∗
          (∃ʰ b,
              (if j + 1 < ↑M ∧ y_ind (j + 1) < y_box 1 then ind ~⟨i in ⟪1, {r}⟫⟩~> val_int (j + 1)
                else ∃ʰ (j : ℤ), ind ~⟨x in ⟪1, {r}⟫⟩~> j ∗ ⌜0 ≤ j ∧ (j < ↑M → y_box 1 ≤ y_ind j)⌝) ∗
                ⌜0 ≤ j + 1 ∧ j + 1 ≤ ↑M ∧ (cond (j + 1) ↔ b = true)⌝) ∗ arr⟨⋆⟩(xind, x in N => x_ind x) ∗
  arr⟨⋆⟩(xid,  x in N => x_id x)
            }) := by stop
    move=> *
    yin 1: yapp
    yapp mem_spec_term; rotate_left
    { apply y_prt_mon=> /== //' }
    { srw -y_ptr0; apply y_prt_mon=> /== //' }
    { srw -y_ptrM; apply y_prt_mon=> /== //' }
    { apply StrictMonoOn.injOn; apply x_ind_mon=> /== //' }
    ysimp[decide (cond (j + 1))]=> /== //'
    { move=> i ??
      srw -(Set.ncard_empty (α := ℝ×ℝ)) ; congr
      move=> ! [??] /==  ->; simp [Box]
      move=> ? *; exfalso; linarith }
    scase_if=> //' /== ?; ysimp=> ⟨|⟩ //'




lemma boxCountQuery'_spec :
  { arr⟨⋆⟩(yind, x in M => y_ind x) ∗
    arr⟨⋆⟩(yptr, x in M + 1 => y_ptr x) ∗

    arr⟨⋆⟩(xind, x in N => x_ind x) ∗
    arr⟨⋆⟩(xid,  x in N => x_id x) ∗

    arr⟨⋆⟩(xbox, x in 2 => x_box x) ∗
    arr⟨⋆⟩(ybox, x in 2 => y_box x) ∗

    arr⟨⟪1, {r}⟫⟩(out, x in K => val_int 0) }
  [1| x in {r} => Lang.boxCountQuery' yptr yind xind xid ybox xbox out]
  [2| ijk in @Set.univ (ℝ × ℝ × ℤ) => Lang.mem2 yptr yind xind xid ⟨ijk.val.1⟩ ⟨ijk.val.2.1⟩ ⟨ijk.val.2.2⟩]
  {v,
    arr⟨⟪1, {r}⟫⟩(out, id in K => val_int ({(i, j) | v ⟨2,i,j,id⟩} ∩ Box y_box x_box).ncard)  ∗ ⊤ } := by
  shave Inj: Set.InjOn y_ind (Set.Ico 0 M)
  { sby apply StrictMonoOn.injOn }
  yfocus 2, (y_ind '' ⟦0, M⟧) ×ˢ ⋆
  yapp mem2_spec_out (y_ind_mono := y_ind_mono); rotate_left
  { exact Set.disjoint_sdiff_left }
  simp [fun_insert]
  yin 1: ystep; ywp; yref ind
  srw [1]Set.image_eq_iUnion biUnion_prod_const
  let op id (hv : hval (ℝ×ℝ×ℤ)ˡ) i := ({y_ind i} ×ˢ {j | hv ⟨2,y_ind i,j,id⟩} ∩ Box y_box x_box).ncard
  let cond (i : ℤ) := i < M ∧ y_ind i < y_box 1
  ywhile+ 0, M with (b₀ := cond 0)
    (Inv := fun b i => (
        if i < M ∧ y_ind i < y_box 1 then
          ind ~⟪1, {r}⟫~> i
        else ∃ʰ (j : ℤ), (ind ~⟪1, {r}⟫~> j) ∗ ⌜0 <= j ∧ (j < M -> y_box 1 <= y_ind j)⌝) ∗
            ⌜0 <= i ∧ i <= M ∧ cond i = b⌝)
    (Q := fun i hv => arr⟨⟪1, {r}⟫⟩(out, id in K => val_int $ op id hv i))
    (H₀ := arr⟨⟪1, {r}⟫⟩(out, x in K => val_int 0)) <;> try simp [op]
  { move=> ?; scase_if; simp [hhlocalE]; srw hhlocal_hhexists; simp [hhlocalE] }
  { move=> > ?? eq; congr! 9; srw eq //' }
  { stop
    move=> > ??
    yin 2:
      ystep; simpWP=> /== ??? L₁;
      (sdo 2 ystep=> //'); ywp; yifT=> /== //'
      sdo 3 (ystep=> //')
    srw if_pos //'
    yin 1:(sdo 4 ystep)
    yin 1: ywp; yif=> /== L₂
    { yin 1:(sdo 5 ystep=> //')
      ysubst with (σ := Prod.snd)
      { ysimp }
      { move=> ?; scase_if; simp [hhlocalE]; srw hhlocal_hhexists; simp [hhlocalE] }
      { move=> /== }
      zapp intervalCountQuery'_spec=> //'
      { apply y_prt_range_j (x_id_range := x_id_range)=> //' }
      { apply y_prt_mon=> /== //' }
      { srw -y_ptr0; apply y_prt_mon=> /== //' }
      { srw -y_ptrM; apply y_prt_mon=> /== //' }
      { apply x_ind_mon=> /== //' }
      yapp; ysimp[decide (cond (j + 1))]=> /== //'
      { clear *-L₁ L₂=> *;
        apply Set.ncard_congr (f := fun x _ => (y_ind j, x))=> /== //'
        move=> > ->; simp [Box]=> -> // }
      scase_if=> /== H * //'
      ysimp=> ⟨//'|?⟩ //' }
    yin 1: yapp
    yapp mem_spec_term; rotate_left
    { apply y_prt_mon=> /== //' }
    { srw -y_ptr0; apply y_prt_mon=> /== //' }
    { srw -y_ptrM; apply y_prt_mon=> /== //' }
    { apply StrictMonoOn.injOn; apply x_ind_mon=> /== //' }
    ysimp[decide (cond (j + 1))]=> /== //'
    { move=> i ??
      srw -(Set.ncard_empty (α := ℝ×ℝ)) ; congr
      move=> ! [??] /==  ->; simp [Box]
      move=> ? *; exfalso; linarith }
    scase_if=> //' /== ?; ysimp=> ⟨|⟩ //' }
  { stop
    move=> > ? jM
    srw LGTM.triple ywp1; ypull=> /== ??; srw cond /== => /(_ (jM)) Le
    ystep; simpWP
    (sdo 2 ystep=> //'); ywp; yifT=> /== //'
    sdo 3 (ystep=> //')
    yapp mem_spec_term; rotate_left
    { apply y_prt_mon=> /== //' }
    { srw -y_ptr0; apply y_prt_mon=> /== //' }
    { srw -y_ptrM; apply y_prt_mon=> /== //' }
    { apply StrictMonoOn.injOn; apply x_ind_mon=> /== //' }
    srw ?if_neg //' /==
    { ypull=> k /== ??
      ysimp=> //'
      { move=> ?? /==; srw -Set.ncard_empty; congr
        move=> ! [??] /== ->; simp [Box]
        move=> ? *; exfalso; linarith }
      move=> ⟨//'|⟨//'|?⟩⟩
      apply le_trans Le; apply le_of_lt; apply y_ind_mono=> /== //' }
    move=> ?; apply le_trans Le; apply le_of_lt; apply y_ind_mono=> /== //' }
  { stop
    move=> > ??
    srw -hwp_equiv; ypull; srw cond=> /== ??
    scase_if=> /== ??
    { ystep; ywp; yapp htriple_lt
      ywp; yifT=> //'; ystep; ystep; yapp
      ysimp=> /==  //' }
    ypull=> k /== ??
    ystep; ywp; yapp htriple_lt
    ywp; yif=> /== ?
    { ystep; ystep; yapp; ysimp=> /== //'; funext=> /== //' }
    ywp; yval; ysimp=> /== //' }
  { stop move=> ?; ypull; srw cond /== => > ?? ->; ysimp=> //' }
  { stop ysimp=> //'; scase_if=> /== //' ?; ysimp=> ⟨|⟩ /== //' }
  ypull; srw cond=> /== > ??; ysimp=> /== //'
  save
  move=> i ??
