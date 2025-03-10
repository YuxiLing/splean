import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records


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
        ⌜L = x::L'⌝ ∗ (p ~~~> `{ head := x; tail := q}) ∗ (MList L' q)) := by sorry


lang_def mnil:= fun u => null

lemma triple_mnil :
  triple [lang| mnil () ]
  (⌜True⌝)
  (funloc p ↦ (MList (List.nil) p) ) := by
  xval; xsimp <;> aesop



--axiom well_founded_ind (A : Type) (R : A -> A -> Prop):
--  ∀ P:A -> Prop,
--    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> ∀ a:A, P a

inductive list_sub : (List val) -> (List val) -> Prop where
| exact (x : val) (L' : List val) : list_sub L' (x::L')


def list_sub_Wf : WellFounded list_sub := by
    constructor
    intro a
    induction a with
    | nil =>
      constructor
      intro y H
      cases H
    | cons x xs ih =>
      constructor
      intro y h
      cases h; apply ih


def measure {α : Type} (f:α->ℕ) : α->α->Prop :=
  fun x1 x2 => (f x1 < f x2)




def measure_Wf (f:α->ℕ) : WellFounded (measure f) :=
  by
    constructor
    intro a
    generalize h : f a = n
    revert a
    induction n using Nat.strong_induction_on with
    | h n' ih =>
      intro a' hh
      constructor
      intro b hhh
      unfold measure at hhh
      apply (ih (f b)) <;> aesop


-- 0 ≤ m < n.
/-
def downto0 (m:ℤ) (n:ℤ) : Prop := 0 ≤ m /\ m < n


def downto_Wf : WellFounded downto0 := by
    constructor
    intro a
    induction a using WellFounded.induction (r:= measure (fun n =>  Int.natAbs (n))) with
    | hwf => apply (measure_Wf (fun n =>  Int.natAbs n))
    | h x' h =>
      constructor
      intro y' H
      apply h
      simp[measure]
      unfold downto0 at H
      omega
-/
/-
def downto0 (m:ℤ) (n:ℤ) : Prop := 0 ≤ m /\ m < n


def downto_Wf : WellFoundedRelation ℤ where
  rel := (downto0)
  wf  := by
    constructor
    intro a
    induction a using WellFounded.induction (r:= measure (fun n =>  Int.natAbs (n))) with
    | hwf => apply (measure_Wf (fun n =>  Int.natAbs n)).wf
    | h x' h =>
      constructor
      intro y' H
      apply h
      simp[measure]
      unfold downto0 at H
      omega

-/
def upto (b:ℤ ) :=
  fun (n m:ℤ ) => (n <= b) /\ (m < n)



def upto_Wf (b : ℤ): WellFounded (upto b) :=
by
    constructor
    intro a
    induction a using WellFounded.induction (r:= measure (fun n =>  Int.natAbs (b-n))) with
    | hwf => apply (measure_Wf (fun n =>  Int.natAbs (b-n)))
    | h x' h =>
      constructor
      intro y' H
      apply h
      simp[measure]
      unfold upto at H
      omega




/-
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

lang_def repeat' := fix g f n =>
       let b := (n > 0) in
       if b then
         f ();
         let n2 := n - 1 in
         g f n2 end


-/
/-
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
  | hwf => apply downto_Wf.wf
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
      xsimp <;> aesop
      xsimp <;> aesop
      simp[downto0]
      simp at C
      have aux2 : m >= 1 := by omega
      simp[aux2]
      have aux2 : 0 <= m-1 := by omega
      have aux3 :  m-1 <= n := by omega
      simp[aux2, aux3]
    }
    {
      simp at C
      have aux : m = 0 := by omega
      rw[aux]
      xsimp
      aesop
      xval
      xsimp
    }
-/
set_option maxHeartbeats 900000
lang_def while_upto :=
fix F start finish f =>
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
             [ (f i) ]
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
    --xwp
    --xseq_xlet_if_needed; xstruct_if_needed; apply xif_lemma
