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



lang_def mlength  :=
fix f p =>
       let b := (p = null) in
       if b
         then 0
         else (let q := ⟨val_get_field tail⟩ p in
               let n := f q in
               n + 1)


lemma triple_mlength : forall l (p:loc),
  { MList l p }
  [ mlength p ]
  {r, ⌜r = val_int (l.length)⌝  ∗ (MList l p) } :=
by
intro l
induction l using WellFounded.induction (r:= list_sub) with
| hwf => apply list_sub_Wf
| h l' ih =>
  intros p
  xwp
  xapp triple_eq
  xif
  { simp[is_true]
    intro H
    simp[H]
    xchange MList_if
    xpull
    xval
    xsimp }
  simp[is_true]
  intro H
  xchange MList_if
  simp[H]
  xpull
  intro x' q L' IH
  xstep triple_get_field_hrecord
  xstep IH
  xapp
  xsimp



def my_get (l : List val) (n:ℕ):=
match l with
| [] => 0
| x::xs => match n with
       | 0 => x
       | n+1 => my_get xs n

lang_def mget  :=
fix f p i =>
       let is_empty := p = null in
       if is_empty
       then 0
       else (
        let b := (i = 0) in
        if b
          then ⟨val_get_field head⟩ p
          else (let q := ⟨val_get_field tail⟩ p in
                let i' := i - 1 in
                  f q i'
                ) )


lemma triple_mget : forall l  (p:loc) (i : ℤ), (i >= 0)→
  { MList l p}
  [ mget p i ]
  { r, MList l p ∗ ⌜r=my_get l (Int.natAbs i)⌝ } :=
by
intro l
induction l using WellFounded.induction (r:= list_sub) with
| hwf => apply list_sub_Wf
| h l' ih =>
  intros p i Hi
  xwp
  xapp triple_eq
  xif
  { simp[is_true]
    intro H
    simp[H]
    xchange MList_if
    xpull
    xval
    xsimp <;> simp[my_get]; rfl }
  simp[is_true]
  intro H
  xchange MList_if
  simp[H]
  xpull
  intro x q L' ih
  xstep triple_eq
  xif
  {
    simp[is_true]
    intro HH
    simp[HH]
    xapp triple_get_field_hrecord
    xsimp
    simp[my_get]
   }
  simp[is_true]
  intro HH
  xwp
  xapp triple_get_field_hrecord
  xwp
  xapp triple_sub
  xapp ih
  xsimp
  { omega }
  have tmp : (i-1).natAbs = (i).natAbs-1 := by omega
  have tmp1 : ¬((i).natAbs = 0) := by omega
  rw[my_get]
  generalize ht :  (i).natAbs = y
  cases y
  { aesop }
  { simp; simp[tmp, ht] }










lang_def mrev_aux :=
fix f p1 p2 =>
       let b := (p2 = null) in
       if b
         then p1
         else (
           let p3 := ⟨val_get_field tail⟩ p2 in
           ⟨val_set_field tail⟩ p2 p1;
           f p2 p3)

lang_def mrev :=
fun p => mrev_aux null p



lemma triple_mrev_aux : forall L' L  (p q :loc),
  { MList L p ∗ MList L' q }
  [ mrev_aux p q]
  { r, ∃ʰ (r':loc), ⌜r' = r⌝ ∗ MList (L'.reverse ++L) r' } :=
by
intro l'
induction l' using WellFounded.induction (r:= list_sub) with
| hwf => apply list_sub_Wf
| h l' ih =>
intros l p q
xwp
xapp triple_eq
xif
{ simp[is_true]
  intro H
  simp[H]
  xchange MList_if
  xpull
  xval
  xsimp }
simp[is_true]
intro H
xchange MList_if; simp[H]
xpull
intro x t M HL'0
xstep triple_get_field_hrecord
xstep triple_set_field_hrecord

have R : { MList (x::l) q ∗ MList M t } [mrev_aux q t] { r, ∃ʰ (r':loc), ⌜r' = r⌝ ∗ MList (M.reverse ++ x::l) r' }
:= by
  apply HL'0
  constructor
simp[MList] at R
xapp R
intro r'
xsimp




lemma triple_mrev : forall L (p:loc),
  { MList L p }
  [mrev p]
  {q, ∃ʰ (q':loc), ⌜q'=q⌝ ∗ MList (L.reverse) q' } :=
by
  intro L p
  xwp
  xapp (triple_mrev_aux L [])
  intro r'
  simp
  xsimp
