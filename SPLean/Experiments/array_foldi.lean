import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Common

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun

open Theories prim val trm

lang_def nat_fold_up_aux  :=
  fix aux upto f i acc =>
    if i = upto then acc
    else aux upto f (i + 1) (f i acc)

lang_def nat_fold_up :=
    fun from_ upto f init =>
        nat_fold_up_aux upto f from_ init

lemma nat_fold_up_spec :
    forall (from_ : Int ) (upto : Int) (f : val) (init : loc ) (I : Int -> val -> hProp),
    (forall (i : Int ), from_ <= i -> i < upto ->
        { I i init}
        [ f i init ]
        { v, I (i + 1) v }) ->
    from_ <= upto ->
    {I from_ init}
    [nat_fold_up from_ upto f init]
    {v, I upto v} := by
    intros from_ upto f init I Hf Hle
    xwp
    have tmp : (
           forall (upto : Int) (f : val) (i: Int) (acc: val),
             from_ <= i /\ i <= upto ->
             {I i acc}
             [(nat_fold_up_aux upto f i acc)]
             { res,  I upto res }
    ) := by
        intros upto ff i acc H1
        simp [nat_fold_up_aux]
        xwp
        sorry


    xapp tmp


lang_def array_foldi :=
    fun arr init f =>
        let n := len arr in
        ref res := init in
        for i in [0:n] {
            res := f i arr[i] !res
        };
        !res

def array_foldisb (l:List val) (fp: val -> val -> val) (init : val) : val :=
  match l with
  | [] => init
  | a::l => (array_foldisb l fp (fp init a))


set_option maxHeartbeats 900000
lemma array_foldi_spec :
  forall (a : loc) (l : List val) (f : val) (fp: val -> val -> val) (init : Int),
    (forall a,
        { ⌜True ⌝}
        [(f a)]
        {b, ⌜b = fp a init⌝ } ) ->
  { harray l a }
  [ array_foldi a init f ]
  { b, ⌜b = array_foldisb l fp init ⌝  ∗  harray l a  } :=
by
  sorry
