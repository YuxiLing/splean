import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records


section find_index

open Theories prim val trm


def fst: field := 0
def snd : field := 1



/- First we put simple triple lemmas into our hint data base
   Those lemmas tell how to symbolically advance basic language instructions -/

#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get


namespace Lang


def MList (L: List val) (p:loc) : hProp :=
  match L with
  | List.nil => ⌜p = null⌝
  | List.cons x L' => ∃ʰ (q:loc), (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q)

lemma MList_nil : ∀ p,
  (MList List.nil p) = ⌜p = null⌝ :=
by aesop

lemma MList_cons : ∀ p x L',
  MList (x::L') p = ∃ʰ (q:loc), (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q) :=
by aesop


lemma MList_if : ∀ (p:loc) (L:List val),
      (MList L p)
  ==> (if p = null
        then ⌜L = []⌝
        else ∃ʰ x, ∃ʰ (q:loc), ∃ʰ L',
        ⌜L = x::L'⌝ ∗ (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q)) := by sorry


lang_def mnil:= fun u => null

lemma triple_mnil :
  triple [lang| mnil () ]
  (⌜True⌝)
  (funloc p ↦ (MList (List.nil) p) ) :=
by
  xval
  xsimp
  { aesop }
  { intro; dsimp[MList_nil null]; xsimp }



axiom well_founded_ind (A : Type) (R : A -> A -> Prop):
  ∀ P:A -> Prop,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> ∀ a:A, P a

inductive list_sub : (List val) -> (List val) -> Prop where
| exact (x : val) (L' : List val) : list_sub L' (x::L')




#check tail

lang_def append := fix f p1 p2 =>
       let q1 := ⟨val_get_field tail⟩ p1 in
       let b := (q1 = null) in
       if b
         then ⟨val_set_field tail⟩ p1 p2
         else f q1 p2




lemma triple_append (p1 p2 : loc) (L1 L2 : List val): ¬(p1 = null) →
(triple  [lang| append p1 p2 ] ((MList L1 p1) ∗ (MList L2 p2))
(fun _ =>  (MList (L1++L2) p1))) :=
by
  intro N
  revert p1
  induction L1 with
  | nil =>
    intro p1 contra
    xwp
    xchange (MList_if p1)
    scase_if
    {intro H; simp[contra] at H }
    { intro H; xpull; intro _ _ _ contra; simp at contra }
  | cons x' L' ih =>
    intro p1 H
    xwp
    xchange (MList_if p1)
    scase_if
    { intro H1; simp[H] at H1}
    { intro H1
      xpull
      intro x q1 L1' HH
      simp at HH
      simp[HH]
      xapp triple_get_field_hrecord
      xwp
      xchange (MList_if q1)
      xapp triple_eq
      simp[is_true]
      scase_if
      {
        intro Hq1
        xif
        {
          intro is_true
          xapp triple_set_field_hrecord
          simp[MList_cons]
          xsimp
        }
        {
          intro contra
          simp at contra
        }
      }
      {
        intro h
        xif
        { intro contra; simp at contra }
        {
           intro _
           xpull
           intro x_1 q L'_1 hs
           simp[XSimp]
           xsimp
           simp[MList]
           xapp (ih)
           simp[hs, MList]
           xsimp
        }
      }
    }
