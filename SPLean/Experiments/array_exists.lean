import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records

import SPLean.Experiments.List

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
    let r := while_upto 0 N (fun i =>
      let tmp := a[i] in
        result := f tmp;
      let tmp_result := !result in
        not tmp_result) in
      let res := !result in
        res


def existsb (l:List val) (fp: val -> Bool) : Bool :=
      match l with
        | [] => false
        | a::l => fp a || existsb l fp



lemma array_exists_spec :
  forall (a : loc) (f : val) (l : List val) (fp: val -> Bool) (N : Int),
    (N = l.length) →
    (forall a,
        { ⌜True ⌝}
        [(f a)]
        {b, ⌜b = fp a⌝} ) ->
  { harray l a }
  [ array_exists a f N ]
  { b, ⌜b = existsb l fp⌝  ∗  harray l a  } :=
by
  intro a f l fp N H Hf
  xref
  xwp
  xlet
  xapp (while_upto_spec 0 l.length _ (fun (i: ℤ) (b: Bool) => ⌜b = Bool.not (existsb (l.take (Int.natAbs i)) fp)⌝  ∗
                         p ~~> (existsb (l.take (Int.natAbs i)) fp) ∗
                         harray l a))
  { intro i Hl
    xwp
    xlet
    xapp
    xval
    xsimp
    sorry
    }
  {
    intro i H
    xwp
    xlet
    xwp
    sorry

   }
