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

@[simp]
def MList (L: List val) (p:loc) : hProp :=
  match L with
  | List.nil => ⌜p = null⌝
  | List.cons x L' => ∃ʰ (q:loc), (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q)

lemma MList_nil : ∀ p,
  (MList List.nil p) = ⌜p = null⌝ := by aesop

lemma MList_cons : ∀ p x L',
  MList (x::L') p = ∃ʰ (q:loc), (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q) := by aesop

/-
we need to add condition (p ≠ null) to hheader definition, but now it's just axiom
-/
axiom hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p ∗ ⌜p ≠ null⌝


lemma MList_if : ∀ (p:loc) (L:List val),
      (MList L p)
  ==> (if p = null
        then ⌜L = []⌝
        else ∃ʰ x, ∃ʰ (q:loc), ∃ʰ L',
        ⌜L = x::L'⌝ ∗ (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q)) :=
by
  intros p L
  cases L with
  | nil =>
    simp[MList_nil]
    xpull
    xsimp
  | cons x xs =>
    simp[MList_cons]
    xpull
    intros q
    xchange hrecord_not_null
    intros N
    scase_if
    { intro contra; aesop }
    { intro _; xsimp; aesop }


lang_def mnil:= fun u => null

lemma triple_mnil :
  triple [lang| mnil () ]
  (⌜True⌝)
  (funloc p ↦ (MList (List.nil) p) ) := by
  xval; xsimp <;> aesop




lang_def append := fix f p1 p2 =>
       let q1 := ⟨val_get_field tail⟩ p1 in
       let b := (q1 = null) in
       if b
         then ⟨val_set_field tail⟩ p1 p2
         else f q1 p2


lemma triple_append (p₁ p₂ : loc) (l₁ l₂ : List val) :
  ¬(p₁ = null) →
  { MList l₁ p₁ ∗ MList l₂ p₂ }
    [append p₁ p₂]
  {_, MList (l₁ ++ l₂) p₁ } := by
  intros
  induction l₁ using WellFounded.induction (r:= list_sub) generalizing p₁ with
  | hwf => apply list_sub_Wf
  | h l' ih =>
      xwp
      xchange (MList_if p₁)
      scase_if
      {intro _; aesop }
      intro
      xsimp; intro x''' q l'' H
      xapp triple_get_field_hrecord
      xstep triple_eq
      xif <;> simp [is_true]
      { intro; simp [*] at *
        xapp triple_set_field_hrecord
        xchange MList_if (L := l'')
        xsimp; xsimp }
      intros; xapp H; xsimp

#check ∀ a, (null ~~> a) ==> ⌜False⌝
