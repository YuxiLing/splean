-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Util
import Lgtm.HProp
import Lgtm.HHProp
import Lgtm.XSimp
import Lgtm.SepLog

section HSepLog

open Classical

variable {α : Type}

def htrm := α -> trm
def hval := α -> val

local notation "hheap"  => @hheap α
local notation "hhProp" => @hhProp α
local notation "htrm"   => @htrm α
local notation "hval"   => @hval α

open trm val

section heval

def heval_nonrel (s : Set α) (hh : hheap) (ht : htrm) (hQ : α -> val -> hProp) : Prop :=
  ∀ a ∈ s, eval (hh a) (ht a) (hQ a)

@[simp]
noncomputable def fun_insert {α β} (f g : α -> β) (s : Set α ) :=
  fun a => if a ∈ s then f a else g a

notation f " ∪_" s:max g => fun_insert f g s

lemma fun_insert_ss :
  ((f ∪_s g) ∪_s h) = f ∪_s h := by
    sby move=> !? /=; scase_if

lemma fun_insert_ff :
  (f ∪_s f) = f := by
    sby move=> !?


lemma fun_insert_ss' :
  (f ∪_s g ∪_s h) = f ∪_s h := by
    sby move=> !? /=; scase_if


lemma fun_insert_assoc :
  ((f ∪_s₁ g) ∪_(s₁ ∪ s₂)  h) = f ∪_s₁ g ∪_s₂ h := by
    sby move=> !? /==; scase_if=> //; scase_if

-- lemma fun_insert_sU :
--   (f ∪_s₁ f ∪_s₂ h) = f ∪_s h := by
--     sby move=> !? /=; scase_if


def heval (s : Set α) (hh : hheap) (ht : htrm) (hQ : hval -> hhProp) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    heval_nonrel s hh ht hQ' ∧
    ∃ hv', ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> hQ (hv ∪_s hv')

lemma heval_nonrel_conseq (s : Set α) :
  heval_nonrel s hh t Q1 →
  (∀ a, qimpl (Q1 a) $ Q2 a) →
  heval_nonrel s hh t Q2 := by
  sby move=> hev qimp a /hev/eval_conseq /(_ (qimp a))

lemma heval_conseq :
  heval s hh t Q1 →
  Q1 ===> Q2 →
  heval s hh t Q2 := by
  scase! => ??? himp qimp ⟨//|⟩
  sby constructor=> // ⟨//|??/himp/qimp⟩

lemma heval_nonrel_frame :
  heval_nonrel s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval_nonrel s (hh1 ∪ hh2) t (fun a => Q a ∗ (fun hh ↦ hh = hh2 a)) := by
  sby move=> hev ?? /hev /eval_frame

lemma heval_frame :
  heval s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval s (hh1 ∪ hh2) t (Q ∗ (· = hh2)) := by
  scase! => hQ *
  exists fun a => hQ a ∗ (· = hh2 a)=> ⟨|⟨//|?⟩⟩
  { sby apply heval_nonrel_frame }
  srw qstarE hqstarE -bighstarDef_hhstar // bighstarDef_eq
  sby apply hhimpl_hhstar_trans_l

lemma heval_prod (hQ : α -> val -> hProp) :
  (∀ a, eval (hh a) (ht a) (hQ a)) ->
  heval s hh ht fun hv => bighstarDef s (fun a => hQ a (hv a)) hh := by
  move=> hev; exists hQ=> ⟨|⟨?//|⟩?/=⟩ //
  sby move=> hh /[swap]a/(_ a); scase_if

lemma heval_nonrel_split :
  heval_nonrel s₁ hh ht hQ ->
  heval_nonrel s₂ hh ht hQ ->
  heval_nonrel (s₁ ∪ s₂) hh ht hQ := by
  sby move=> hev₁ hev₂ ? /== [/hev₁|/hev₂]

lemma heval_nonrel_split1 :
  heval_nonrel (s₁ ∪ s₂) hh ht hQ ->
  heval_nonrel s₁ hh ht hQ := by
  sby move=> /[swap]?/[swap]?; sapply

lemma eval_sat :
  eval h t Q -> ∃ h v, Q h v := by sorry

lemma heval_nonrel_sat :
  heval_nonrel s h t Q ->
    ∃ (hh : hheap) (hv : hval), ∀ a ∈ s, Q a (hv a) (hh a) := by sorry


lemma heval_unfocus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval (s₁ ∪ s₂) hh ht hQ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) := by
  move=> /Set.disjoint_left dj ![hQ₁ hev] /= hv himp
  exists (fun a => if a ∈ s₁ then hQ₁ a else (fun _ => (· = hh a)))
  constructor=> [|⟨//|⟩hv/= hh' /= H']
  { sby move=> ?? /=; scase_if }
  exists (fun a => if a ∈ s₂ then hQ₁ a else (fun _ => (· = hh' a)))
  constructor
  { move=> a /[dup]/dj/=; scase_if=> //== ??
    sby move: (H' a); scase_if=> // ? ->; apply hev }
  move=> ⟨//|⟩ hv' /=
  srw fun_insert_ss -fun_insert_assoc
  apply hhimpl_trans_r; apply himp
  move=> hh /= /[swap] a /(_ a) /==
  sby move: (H' a); scase_if

lemma heval_focus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) ->
  heval (s₁ ∪ s₂) hh ht hQ := by
  move=> /Set.disjoint_left dj ![hQ₁ hev hv'] /= himp
  scase!: (heval_nonrel_sat hev)=> hh' hv H
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_=> //; scase!: H=> hQ₂ hev' hv' /= himp'
  exists (fun a => if a ∈ s₁ then hQ₁ a else hQ₂ a)=> ⟨|⟩
  { apply heval_nonrel_split=> [a|a /[dup]?/dj] /=; scase_if=> //
    sby move: (hev' a)=> // }
  exists hv'; clear hv H himp'=> hv hh' H'
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_
  { sby move=> a; scase_if=> //; move: (H' a)=> /==; scase_if }
  scase: H=> hQ₂' /= ![? hv2]
  srw fun_insert_ss -fun_insert_assoc=> /(_ hv)/fun_insert_ff












end heval


end HSepLog
