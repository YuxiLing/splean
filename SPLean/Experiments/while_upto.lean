import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records

import SPLean.Experiments.induction_wf
--section find_index

open Theories prim val trm


def fst: field := 0
def snd : field := 1




#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get

#hint_xapp triple_gt

namespace Lang


set_option maxHeartbeats 1200000
lang_def while_upto :=
fix F start finish f   =>
  let cond := start = finish in
  if cond
  then true
  else (
    let tmp_inner_cond := f start in
      let inner_cond := not(tmp_inner_cond) in
          if inner_cond
          then false
          else let start_plus_1 := start + 1 in F start_plus_1 finish f
    )


lemma while_upto_spec:
  forall (start finish) (f)
         (I: Int -> Bool -> hProp),
         (forall (i: Int),
             start <= i /\ i < finish ->
             { I i true }
             [ (f i ) ]
             { b, ∃ʰ (b':Bool), ⌜b'=b⌝ ∗ I (i + 1) b' }
         ) -> start <= finish ->
   { I start true }
   [ while_upto start finish f ]
   { b,  ∃ʰi, ∃ʰ (b':Bool), ⌜i <= finish /\ b'= b /\ (b' → (i = finish))⌝  ∗  I i b' }
:=
by
  intro start finish f I
  induction start using WellFounded.induction (r:= upto finish) with
  | hwf => apply (upto_Wf finish)
  | h s' ih =>
    intro HI Hlen
    xwp
    xlet
    xstep triple_eq
    xif
    {
      intro C
      simp[is_true] at C
      xsimp
      xval
      xsimp
      aesop
    }
    {
      intro C
      simp[is_true] at C
      xsimp
      xwp
      xlet
      xwp
      xapp HI
      { intro b'
        xwp
        xlet
        xapp triple_neg
        xif
        {
          intro C'
          simp at C'
          xsimp
          xval
          xsimp
          apply And.intro; omega; apply And.intro; simp; simp
        }
        {
          intro C'
          simp at C'
          xsimp
          xwp
          xapp triple_add
          xapp ih; intro i b'' H; xsimp
          simp[upto]; omega
          intro i h; apply HI; omega; omega; apply H

        }
      }
      {
        omega
      }
    }
