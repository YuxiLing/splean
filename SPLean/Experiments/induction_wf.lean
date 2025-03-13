import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records


open Theories prim val trm





namespace Lang


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
