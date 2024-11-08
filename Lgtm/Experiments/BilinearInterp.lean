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

theorem biUnion_prod_const (s': Finset ι) {s : ι → Set α} {t : Set β} :
  (⋃ i ∈ s', s i) ×ˢ t = ⋃ i ∈ s', s i ×ˢ t := by
  ext
  simp=> ⟨|⟩ ![] // ![] //


@[app_unexpander val.toReal] def unexpandToInt : Lean.PrettyPrinter.Unexpander
  | `($_ $v) => `($v)
  | _ => throw ( )

attribute [-simp] fun_insert Bool.forall_bool
attribute [simp] Set.univ_inter

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

lang_def condition :=
  fun cnt xleft intr n =>
    let i := !cnt in
    let inBounds := i < n in
    if inBounds then
      let l := xleft[i] in
      l < intr
    else false

lang_def max :=
  fun x y =>
  let cnd := y >= x in
    if cnd then y else x

lang_def min :=
  fun x y =>
  let cnd := y >= x in
    if cnd then x else y

lang_def int_length :=
  fun xleft xright i intl intr =>
    let indl := xleft[i] in
    let indr := xright[i] in
    let indl := max intl indl in
    let indr := min intr indr in
    indr - indl

lang_def body :=
  fun cnt xleft xright xval z n intl intr ans =>
    let i := !cnt in
    let r := xright[i] in
    let cnd := r >= intl in
    if cnd then
      let ln := int_length xleft xright i intl intr in
      let v := xval[i] in
      let v    := v * ln in
      ans += v
    else ()

lang_def Lang.linearInterp' :=
  fun xleft xright xval z n intl intr ans =>
    ref cnt := z in
    while (condition cnt xleft intr n) {
      body cnt xleft xright xval z n intl intr ans;
      incr cnt
      }

lang_def Lang.get2 :=
  fun xleft xright yprt yleft yright yval i j =>
    let N := len xleft in
    let ind := Lang.searchSRLE xleft xright i 0 N in
    let outOfBounds := (ind = N) in
    if outOfBounds then ⟨0:ℝ⟩
    else
      let yz := yprt[ind] in
      let ind' := ind + 1 in
      let yn := yprt[ind'] in
      Lang.get yleft yright yval j yz yn in

lang_def Lang.bilinearInterp :=
  fun xleft xright yprt yleft yright yval =>
    ref ans := ⟨0 : ℝ⟩ in
    let N := len xleft in
    for i in [0:N] {
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

lang_def body2 :=
  fun cnt yleft yright yprt xleft xright xval z n yintl yintr xintl xintr ans =>
    let i := !cnt in
    let r := yright[i] in
    let cnd := r >= intl in
    if cnd then
      let ln := int_length yleft yright i yintl yintr in
      let yz  := yprt[i] in
      let i' := i + 1 in
      let yn  := yprt[i'] in
      ref ans' := 0 in
      linearInterp' xleft xright xval yz yn xintl xintr ans'
      let ans' := !ans' in
      ans := ans' * v
    else ()

lang_def Lang.bilinearInterp' :=
  fun xleft xright yprt yleft yright yval ans =>
    let N := len xleft in
    ref cnt := ⟨0 : ℝ⟩ in
    while (condition cnt yleft N) {
      body2 cnt yleft yright yprt xleft xright xval z n yintl yintr xintl xintr ans;
      incr cnt
    }

variable (xleft xright xval : loc) (z n : ℤ) (N : ℕ)
variable (x_left x_right : ℤ -> ℝ) (x_val : ℤ -> ℝ)

#hint_yapp triple_hharrayFun_get
#hint_yapp triple_hharrayFun_length
#hint_yapp htriple_eq
#hint_yapp htriple_get
#hint_yapp htriple_subr
#hint_yapp htriple_mulr
#hint_yapp htriple_le
#hint_yapp htriple_ger
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
  -- let lem :=
  ywp; yapp @Lang.searchSRLE_hspec _ k _ _ id=> /== //
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
  ywp; yapp (Lang.searchSRLE_hspec_out (f := id)) => /== //
  ystep; ywp; yifT=> //'
  ywp; yval; ysimp=> //'

open MeasureTheory

attribute [-simp] Finset.mem_Ico
omit zLn oLz nLN in
lemma disj_lr : Set.Pairwise ((Finset.Ico z n)) (Disjoint on fun x ↦ Set.Ico (x_left x) (x_right x)) := by
  move=> x /== ?? y ?? ?
  scase: [x < y]
  { move=> ?; shave: y < x; omega
    move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
    left; right; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //' }
  move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
  right; left; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //'

set_option maxRecDepth 1500 in
set_option maxHeartbeats 1600000 in
lemma linearInterp_spec (r : ℝ)  :
  { arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.linearInterp xleft xright xval z n]
  [2| i in ⋆ => Lang.get xleft xright xval ⟨i.val⟩ z n]
  {v,
    ⌜v ⟨1,r⟩ = ∫ i, (v ⟨2,i⟩).toReal⌝ ∗
    arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) } := by stop
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
  sby apply disj_lr

omit x_lr x_rl zLn oLz nLN in
lemma Set.Ico_inter (a : ℝ) :
  Set.Ico a b ∩ Set.Ico c d = Set.Ico (max a c) (min b d) := by
  srw Set.Ico_inter_Ico=> //


macro_rules | `(ssrTriv| //') => `(tactic| solve | (try simp only [Finset.mem_Ico]); auto)

lemma body_spec_lt (ans : loc) (intl intr : ℝ) :
      z <= j ->
      j < n ->
      x_right j < intl ->
      arr⟨⋆⟩(xval , x in N => x_val x) ∗
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) ∗
      ans ~⟪1, {r}⟫~> v ∗ ind ~⟪1, {r}⟫~> j ==>
        hwp ⟪1,{r}⟫ (fun _ => [lang| body ind xleft xright xval z n intl intr ans])
        fun _ =>
      arr⟨⋆⟩(xval , x in N => x_val x) ∗
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) ∗
      ans ~⟨i in ⟪1, {r}⟫⟩~> v ∗
      ind ~⟨x in ⟪1, {r}⟫⟩~> j := by
      move=> /== ? ?
      (sdo 3 ystep=> //')
      ywp; yifF=> //'; ywp; yval; ysimp=> //'

omit x_lr x_rl zLn oLz nLN in
@[yapp]
lemma min_spec (x y : ℝ) :
  emp ==> hwp ⟪1,{r}⟫ (fun _ => [lang| min x y])
        fun v => ⌜v = fun _ => val_real (min x y)⌝ := by
  ystep; ywp; yif=> /== ? <;> (ywp; yval; ysimp=> /==; funext)=> /==
  apply Eq.symm (min_eq_left ..)=> //
  apply Eq.symm (min_eq_right ..)=> //; linarith

omit x_lr x_rl zLn oLz nLN in
@[yapp]
lemma max_spec (x y : ℝ) :
  emp ==> hwp ⟪1,{r}⟫ (fun _ => [lang| max x y])
        fun v => ⌜v = fun _ => val_real (max x y)⌝ := by
  ystep; ywp; yif=> /== ? <;> (ywp; yval; ysimp=> /==; funext)=> /==
  apply Eq.symm (max_eq_right ..)=> //
  apply Eq.symm (max_eq_left ..)=> //; linarith

omit x_lr x_rl zLn in
@[yapp]
lemma int_length_spec (intl intr : ℝ) :
   z <= j ->
   j < n ->
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) ==>
        hwp ⟪1,{r}⟫ (fun _ => [lang| int_length xleft xright j intl intr])
        fun v => ⌜v = fun _ => val_real ((min intr $ x_right j) - (max intl $ x_left j))⌝  ∗
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) := by
      move=> ??
      sdo 4 ystep
      yapp; ysimp=> //'

omit x_lr x_rl zLn in
set_option maxHeartbeats 1600000 in
lemma body_spec_ge (ans : loc) (intl intr : ℝ) (v : ℝ) :
      z <= j ->
      j < n ->
      x_right j >= intl ->
      arr⟨⋆⟩(xval , x in N => x_val x) ∗
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) ∗
      ans ~⟪1, {r}⟫~> v ∗ ind ~⟪1, {r}⟫~> j ==>
        hwp ⟪1,{r}⟫ (fun _ => [lang| body ind xleft xright xval z n intl intr ans])
        fun _ =>
      arr⟨⋆⟩(xval , x in N => x_val x) ∗
      arr⟨⋆⟩(xright, x in N =>x_right x) ∗
      arr⟨⋆⟩(xleft, x in N => x_left x) ∗
      ans ~⟨i in ⟪1, {r}⟫⟩~> val_real (x_val j * (Min.min intr (x_right j) - Max.max intl (x_left j)) + v) ∗
      ind ~⟨x in ⟪1, {r}⟫⟩~> j := by
      move=> /== ? ?
      (sdo 3 ystep)
      ywp; yifT=> //'
      (sdo 3 ystep)
      yapp
      -- ywp; yifF=> //'; ywp; yval; ysimp=> //'

omit x_lr x_rl zLn in
set_option maxHeartbeats 1600000 in
@[yapp]
lemma condition_spec (intr : ℝ) :
    z <= j ->
    -- j < n ->
    arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    ind ~⟪1, {r}⟫~> j ==>
       hwp ⟪1,{r}⟫ (fun _ => [lang| condition ind xleft intr n])
       fun v =>
         ind ~⟪1, {r}⟫~> j ∗
         ⌜v = fun _ => val_bool (j < n ∧ x_left j < intr)⌝ ∗
         arr⟨⋆⟩(xleft, x in N => x_left x) := by
    ystep; ystep; ywp; yif=> /== ?
    { ystep; yapp htriple_ltr; ysimp=> //' }
    ywp; yval; ysimp=> //'; funext=> //'



set_option maxRecDepth 1500 in
set_option maxHeartbeats 6400000 in
lemma linearInterp'_spec (intl intr : ℝ) (r : ℝ) (ans : loc) (_ : intl ≤ intr) :
  { ans ~⟪1,{r}⟫~> val_real 0 ∗
    arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) }
  [1| x in {r} => Lang.linearInterp' xleft xright xval z n intl intr ans]
  [2| i in Set.Ico intl intr  => Lang.get xleft xright xval ⟨i.val⟩ z n]
  {v,
    ans ~⟪1,{r}⟫~> val_real (∫ i in Set.Ico intl intr, (v ⟨2,i⟩).toReal) ∗
    arr⟨⋆⟩(xleft, x in N => x_left x) ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗
    arr⟨⋆⟩(xval, x in N => x_val x) } := by
  yfocus 2, ⋃ i ∈ ⟦z,n⟧, Set.Ico (x_left i) (x_right i)
  yapp get_spec_out=> //'; rotate_left
  { exact Set.disjoint_sdiff_left }
  simp [fun_insert, OfNat.ofNat, Zero.zero]
  srw Set.inter_iUnion₂; simp [Set.Ico_inter]
  yin 1: ywp; yref ind
  let op := fun (hv : hval ℝˡ) i => ∫ j in Set.Ico (max intl $ x_left i) (min intr $ x_right i), (hv ⟨2,j⟩).toReal
  let P := fun (hv : hval ℝˡ) i => IntegrableOn (fun j => (hv ⟨2,j⟩).toReal) (Set.Ico (max intl $ x_left i) (min intr $ x_right i))
  let cond (i : ℤ) := i < n ∧ x_left i < intr
  let Inv := fun (b : Bool) i =>
    (if i < n ∧ x_left i < intr then
      ind ~⟪1, {r}⟫~> i
    else ∃ʰ (j : ℤ), (ind ~⟪1, {r}⟫~> j) ∗
    ⌜z <= j ∧ (j < n -> intr <= x_left j)⌝) ∗
    ⌜0 <= i ∧ i <= n ∧ cond i = b⌝
  ywhile+. z, n with (b₀ := cond z)
    (Inv := fun (b : Bool) i =>
      (if i < n ∧ x_left i < intr then
        ind ~⟪1, {r}⟫~> i
      else ∃ʰ (j : ℤ), (ind ~⟪1, {r}⟫~> j) ∗
      ⌜z <= j ∧ (j < n -> intr <= x_left j)⌝) ∗
      ⌜0 <= i ∧ i <= n ∧ cond i = b⌝)
    (Q := fun i hv => ans ~⟪1,{r}⟫~> op hv i ∗ ⌜P hv i⌝)
    (H₀ := ans ~⟪1, {r}⟫~> val_real 0) <;> try simp [op, P]
  { move=> ?; scase_if; simp [hhlocalE]; srw hhlocal_hhexists; simp [hhlocalE] }
  { move=> j > /== ?? eq; congr! 2
    { congr! 2; apply setIntegral_congr
      { exact measurableSet_Ico }
      move=> ?? /=; srw eq // }
    apply integrableOn_congr_fun
    { move=> ?? /=; srw eq // }
    exact measurableSet_Ico }
  { move=> > ??
    yin 2:
      yapp get_spec_in (k := j)=> [/== _ _ _ L|]; rotate_left
      { move=> /== //' }
    srw if_pos=> //'; scase: [x_right j < intl]=> /== G
    { ywp; yapp body_spec_ge; yapp
      ysimp[decide (cond (j + 1))]=> /== //' /==
      { move=> ? _ _; srw mul_comm ENNReal.toReal_ofReal /==
        move=> ⟨|⟩ ⟨|⟩ //'; linarith
        apply x_lr=> //' }
      scase_if=> /== //' H; ysimp=> ⟨|⟩ //' }
    ywp; yapp body_spec_lt; yapp
    ysimp[decide (cond (j + 1))]=> /== //' /==
    { move=> ? _ _; srw ENNReal.toReal_eq_zero_iff /==
      left; left; right; linarith }
    scase_if=> /== //' H; ysimp=> ⟨|⟩ //' }
  { move=> > ? jN; srw LGTM.triple ywp1
    yapp get_spec_in (k := j)=> [/== ?? cndE|]; rotate_left
    { move=> /== //' }
    simp [cond] at cndE
    shave ?: j + 1 < n → intr ≤ x_left (j + 1);
    { move=> ?; apply le_trans (cndE jN);
      apply le_trans; apply x_lr=> //'; apply x_rl=> //' }
    srw ?if_neg /== //'
    ypull=> k /== ??
    ysimp=> /== //'
    { move=> ? _ _; srw ENNReal.toReal_eq_zero_iff /==
      left; right; left=> //' }
    srw cond /== => ⟨|⟨|⟩⟩ //' }
  { move=> > ??; scase_if=> L /==
    { yapp; srw cond=> /==  _ _ ?; ysimp=> /== //'
      { funext; scase: b=> /== //' }
      move=> ⟨|⟩ //' }
    srw -hwp_equiv; ypull=> k /== ?? _ _ cndE;
    yapp; ysimp=> /== //'; funext
    { scase: b L; srw cond /== //' => H ? /(_ H) ?;
      exfalso; linarith }
    move=> ⟨|⟩ //' }
  { move=> b; srw cond /==; ysimp=> //' }
  { ysimp=> /== //'
    scase_if=> /== xn; ysimp=> //' }
  ypull=> j *; ysimp=>/== ? _ _
  srw -integral_finset_biUnion //'
  { simp [<-Set.Ico_inter, <-Set.inter_iUnion₂]=> //'
    srw -setIntegral_indicator
    { simp [Finset.mem_Ico, Set.indicator]
      congr!; scase_if=> /== // }
    apply Finset.measurableSet_biUnion=> *
    exact measurableSet_Ico }
  move=> x /== ?? y ?? ?
  scase: [x < y]
  { move=> ?; shave: y < x; omega
    move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
    left; right; right; right; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //' }
  move=> /= /(Lang.left_right_monotone_rl _ _ x_lr x_rl) L
  right; right; left; right; apply le_of_lt; apply L <;> simp [Finset.mem_Ico]=> //'


end Unary
@[simp]
lemma img_sep (f : α -> α') (g : β -> β') :
  (fun x => (f x.1, g x.2)) '' s ×ˢ s' = (f '' s) ×ˢ (g '' s') := by
  move=> ! [a b]=> /== ⟨![] a  b ? <-<- ⟨|⟩|[![]] a ? <- ![] b ? <-⟩
  { exists a=> // }
  { exists b=> // }
  exists a, b=> //'

section Binary

variable (xleft xright yprt yleft yright yval : loc)
variable (x_left x_right y_left y_right : ℤ -> ℝ) (y_ptr : ℤ -> ℤ) (y_val : ℤ -> ℝ)
variable (N : ℕ) (NG0 : N > 0)

variable (x_lr : ∀ i ∈ ⟦0, N⟧, x_left i < x_right i)
variable (x_rl : ∀ i ∈ ⟦0, N-1⟧, x_right i <= x_left (i + 1))

variable (y_ptr_mon : StrictMonoOn y_ptr ⟦0, N+1⟧)
variable (y_ptr_N : y_ptr N = N + 1) (y_ptr_0 : y_ptr 0 = 0)

variable (y_lr : ∀ i ∈ ⟦0,N⟧, ∀ j ∈ ⟦y_ptr i, y_ptr (i + 1)⟧, y_left j <= y_right j)
variable (y_rl : ∀ i ∈ ⟦0,N⟧, ∀ j ∈ ⟦y_ptr i, y_ptr (i + 1)-1⟧, y_right j <= y_left (j + 1))

include NG0 x_lr x_rl y_ptr_mon y_ptr_N y_ptr_0 y_lr y_rl

omit y_ptr_mon y_ptr_0 y_lr y_rl in
set_option maxHeartbeats 1600000 in
lemma get2_spec_out (s : Set (ℝ × ℝ)) :
  Disjoint s ((⋃ i ∈ ⟦0, N⟧, Set.Ico (x_left i) (x_right i)) ×ˢ ⋆) ->
  arr⟨⟪l,s⟫⟩(xleft , x in N => x_left x)  ∗
  arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) ==>
  WP [l| ij in s => Lang.get2 xleft xright yprt yleft yright yval ⟨ij.val.1⟩ ⟨ij.val.2⟩] { v,
    ⌜v = fun _ => val_real 0⌝ ∗
    arr⟨⟪l,s⟫⟩(xleft , x in N => x_left x)  ∗
    arr⟨⟪l,s⟫⟩(xright, x in N => x_right x) } := by
    move=> /Set.disjoint_left dj; ystep
    ywp; yapp Lang.searchSRLE_hspec_out=> //'
    { ystep; ywp; yifT=> //'; ywp; yval; ysimp=> //' }
    { move=> ? /x_lr /le_of_lt //' }
    srw Set.disjoint_left=> ?; simp [-Set.mem_iUnion, -Finset.mem_Ico]
    move=> ? /dj; simp [-Set.mem_iUnion, -Finset.mem_Ico]

attribute [-simp] Finset.mem_Ico Set.singleton_prod

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

open MeasureTheory


set_option maxRecDepth 2000 in
set_option maxHeartbeats 6400000 in
lemma bilinearInterp_spec  :
  { arr⟨⋆⟩(xleft , x in N => x_left x)  ∗
    arr⟨⋆⟩(xright, x in N => x_right x) ∗

    arr⟨⋆⟩(yprt  , x in N+1 => y_ptr x)   ∗
    arr⟨⋆⟩(yleft , x in N+1 => y_left x)  ∗
    arr⟨⋆⟩(yright, x in N+1 => y_right x) ∗

    arr⟨⋆⟩(yval  , x in N+1 => y_val x) }
  [1| x in {(r₁, r₂)}         => Lang.bilinearInterp xleft xright yprt yleft yright yval]
  [2| ij in @Set.univ (ℝ × ℝ) => Lang.get2 xleft xright yprt yleft yright yval ⟨ij.val.1⟩ ⟨ij.val.2⟩]
  {Grid,
    ⌜Grid ⟨1,r₁,r₂⟩ = ∫ (i : ℝ) (j : ℝ), (Grid ⟨2,i,j⟩).toReal⌝ ∗ ⊤ } := by stop
    yfocus 2, (⋃ i ∈ ⟦0, N⟧, Set.Ico (x_left i) (x_right i)) ×ˢ ⋆
    yapp get2_spec_out; rotate_left
    { exact Set.disjoint_sdiff_left }
    simp [fun_insert, OfNat.ofNat]; simp [Zero.zero]
    yin 1: ywp; yref ans; ystep; simp [OfNat.ofNat]; simp [Zero.zero, One.one]
    srw biUnion_prod_const
    let op := fun (hv : hval (ℝ×ℝ)ˡ) i => ∫ i in Set.Ico (x_left i) (x_right i), ∫ j, (hv ⟨2,i,j⟩).toReal
    let P := fun (hv : hval (ℝ×ℝ)ˡ) i => IntegrableOn (fun i => ∫ j, (hv ⟨2,i,j⟩).toReal) (Set.Ico (x_left i) (x_right i))
    yfor+. with
      (Q := fun i hv => ans ~⟪1, {(r₁, r₂)}⟫~> op hv i ∗ ⌜P hv i⌝)
      (H₀ := ans ~⟪1,{(r₁, r₂)}⟫~> val_real 0)<;> try simp [op, P]
    { move=> j > /== ?? eq; congr! 2
      { congr! 2; apply setIntegral_congr
        { exact measurableSet_Ico }
        move=> ?? /=; refine integral_congr_ae ?h
        filter_upwards with a; srw eq // }
      apply integrableOn_congr_fun
      { move=> ?? /=; refine integral_congr_ae ?h
        filter_upwards with a; srw eq // }
      exact measurableSet_Ico }
    { move=> i r ??
      yin 1: sdo 6 ystep=> //'
      yin 2:
        ystep
        ywp; yapp Lang.searchSRLE_hspec (i := i); rotate_left
        { move=> ? /x_lr /le_of_lt //' }
        { simp [Finset.mem_Ico]=> // }
        { move=> ? /== // }
        ystep; ywp; yifF=> /== //'
        sdo 3 ystep=> //'
      ymerge 2 with (μ := fun x => ⟨x_left i, x.2⟩)
      { apply x_lr; simp [Finset.mem_Ico]=> // }
      { move=> [] /== > ?? <- ⟨//'|⟩; apply x_lr; simp [Finset.mem_Ico]=> // }
      erw [(img_sep (f := fun _ => x_left i) (g := id)), Set.Nonempty.image_const]=> /==; rotate_left
      { apply x_lr; simp [Finset.mem_Ico]=> // }
      ysubst with (σ := Prod.snd)
      { ysimp }
      { scase; simp }
      zapp linearInterp_spec
      { apply y_lr; simp [Finset.mem_Ico]=> // }
      { apply y_rl; simp [Finset.mem_Ico]=> // }
      { apply y_ptr_mon=> /== // }
      { srw -y_ptr_0; srw StrictMonoOn.le_iff_le=> //' /== //' }
      { srw /== -y_ptr_N; srw StrictMonoOn.le_iff_le=> //' /== //' }
      move=> ->; ystep; yapp; ysimp
      move=> ? _; srw mul_comm ENNReal.toReal_ofReal;
      specialize x_lr i ?_; simp [Finset.mem_Ico]=> //
      linarith }
    { ysimp }
    yapp=> ?; ysimp=> /==
    srw -integral_finset_biUnion //'
    { srw -[2](setIntegral_eq_integral_of_forall_compl_eq_zero
               (s := ⋃ i ∈ ⟦0, N⟧, (Set.Ico (x_left i) (x_right i))))
      { apply setIntegral_congr=> [|?]//
        apply Finset.measurableSet_biUnion=> //' }
      move=> /== ??;
      srw integral_congr_ae ?integral_zero
      filter_upwards=> ?; srw if_neg // }
    apply disj_lr=> //' ? /x_lr /le_of_lt //'



end Binary
