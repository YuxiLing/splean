import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records
import SPLean.Experiments.induction_wf

--section find_index

open Theories prim val trm

-- test
#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get

#hint_xapp triple_gt


namespace Lang


lang_def repeat' := fix g f n =>
       let b := (n > 0) in
       if b then
         f ();
         let n2 := n - 1 in
         g f n2 end




set_option maxHeartbeats 300000
lemma triple_repeat_aux : ∀ (I:Int → hProp) (f:val) (n:Int),
  n ≥ 0 →
  (∀ i, 0 ≤ i /\ i < n →
    { I i }
    [ f () ]
    { _, I (i+1) } ) →
  (∀ m, 0 ≤ m /\ m ≤ n →
      { I (n-m) }
      [ (repeat' f m) ]
      { _ , I n } ) := by
  intro I f n Hn Hf m
  induction m using WellFounded.induction (r:= downto0) with
  | hwf => apply downto_Wf
  | h m h =>
    intro Hm
    xwp
    xapp
    xif <;> intro C
    { have aux : 0 ≤ (n-m) ∧ (n-m) < n := by aesop
      xstep Hf (n-m)
      xwp
      xapp
      xapp h
      have aux1 : n - m + 1 = n - (m-1) := by omega
      xsimp <;> simp_all only [ge_iff_le, and_imp, decide_eq_true_eq, sub_nonneg, sub_lt_self_iff, and_self]
      xsimp
      simp[downto0]
      simp at C
      have aux2 : m >= 1 := by omega
      simp[aux2]
      have aux2 : 0 <= m-1 := by omega
      have aux3 :  m-1 <= n := by omega
      simp[aux2, aux3]
      omega
      simp[downto0]; omega
    }
    {
      simp at C
      have aux : m = 0 := by omega
      rw[aux]
      xsimp
      simp_all only [ge_iff_le, and_imp, le_refl, true_and, sub_zero]
      xval
      xsimp
    }
