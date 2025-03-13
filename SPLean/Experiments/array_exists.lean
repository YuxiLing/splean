import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records

import SPLean.Experiments.while_upto

--section find_index

open Theories prim val trm




/- First we put simple triple lemmas into our hint data base
   Those lemmas tell how to symbolically advance basic language instructions -/

#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get

#hint_xapp triple_gt


namespace Lang





lang_def array_exists  :=
fun a f N =>
  ref result := false in
    let my_fun := (fun_ i/-a result f-/=>
      let tmp := a[i] in
        let tmp1 := f tmp in
          result := tmp1;
      let tmp_result := !result in
        not tmp_result) in
    let r := (while_upto 0 N my_fun/-(fun_ i/-a result f-/=>
      let tmp := a[i] in
        let tmp1 := f tmp in
          result := tmp1;
      let tmp_result := !result in
        not tmp_result)-/ /-a result f-/ ) in
      let res := !result in
        res

#print array_exists

def existsb (l:List val) (fp: val -> Bool) : Bool :=
      match l with
        | [] => false
        | a::l => fp a || existsb l fp

lemma existb_spec  (l:List val) (fp: val -> Bool) :
∀i, existsb (List.take i l) fp = true → existsb l fp :=
by
  intro i H
  induction l generalizing i with
  | nil => simp[existsb] at H
  | cons x xs ih =>
    cases i with
    | zero => simp[existsb] at H
    | succ i' => simp[List.take_succ_cons, existsb] at H; simp[existsb]; aesop

lemma existb_spec1  (l:List val) (fp: val -> Bool) (i:ℕ) (h : i < l.length) :
existsb (List.take i l) fp = false →  existsb (List.take (i+1) l) fp = fp l[i]! :=
by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp[existsb]
    | succ i' => simp[List.take_succ_cons, existsb]; aesop



--#hint_xapp triple_array_get
#eval List.take 1 [1,2,3]




set_option maxHeartbeats 900000
lemma array_exists_spec :
  forall (a : loc) (f : val) (l : List val) (fp: val -> Bool) (N : Int),
    (N = l.length) →
    (forall a,
        { ⌜True ⌝}
        [(f a)]
        {b, ⌜b = fp a⌝ } ) ->
  { harray l a }
  [ array_exists a f N ]
  { b, ⌜b = existsb l fp⌝  ∗  harray l a  } :=
by
  intro a f l fp N H Hf
  xref
  xwp
  xlet
  xwp
  xseq_xlet_if_needed; xstruct_if_needed;
  apply xfun_nospec_lemma
  intro ff Hnested
  xwp
  xapp (while_upto_spec 0 l.length _ /-a p f-/ (fun (i: ℤ) (b: Bool) => ⌜b = Bool.not (existsb (l.take (Int.natAbs i)) fp)⌝  ∗
                         p ~~> (existsb (l.take (Int.natAbs i)) fp) ∗
                         harray l a) )
  { --simp[XSimp]

    intro i Hl
    xwp
    xlet
    xapp
    xval
    xsimp
    generalize h : (existsb (List.take i.natAbs l) fp) = m
    cases (m)
    { simp[h] at Hl; simp[Hl] at h; simp[h] }
    { apply existb_spec at h
      simp[h] } }
  { intro i H

    xapp (Hnested i (⌜true = (existsb (List.take i.natAbs l) fp).not⌝ ∗ p ~~> existsb (List.take i.natAbs l) fp ∗ harray l a)
    (fun b =>
    ∃ʰ b',
      ⌜b' = b⌝ ∗
        ⌜b' = (existsb (List.take (i + 1).natAbs l) fp).not⌝ ∗
          p ~~> existsb (List.take (i + 1).natAbs l) fp ∗ harray l a ))

    { intro _; xsimp; simp }

    xwp
    xsimp
    intro h
    xapp triple_array_get
    xwp
    xlet
    xwp
    xapp Hf
    xstep triple_set
    xwp
    xlet
    xstep triple_get
    xapp triple_neg

    xsimp
    { aesop }
    repeat'
    { apply existb_spec1 at h;
      have tmp : (i + 1).natAbs = i.natAbs + 1 := by omega;
      simp[tmp]
      apply Bool.not_inj;  aesop; omega } }
