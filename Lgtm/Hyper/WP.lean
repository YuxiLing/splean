import Lean

-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.WP

import Lean



import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
-- import Lgtm.Hyper.WPUtil


section HWeakestPrecondition

open Classical trm val prim

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

/- ---------- Definition and Structural Rules for [wp] ---------- -/

/- Definition of [wp] -/


def hwp (ht : htrm) (Q : hval -> hhProp) : hhProp := (heval s · ht Q)

/- Equivalence b/w [wp] and [triple] -/

lemma hwp_equiv : H ==> hwp s ht Q = htriple s ht H Q := by rfl

/- Consequence rule for [wp] -/
lemma hwp_conseq (ht : htrm) (Q Q' : hval -> hhProp) :
  Q ===> Q' -> hwp s ht Q ==> hwp s ht Q' := by
  sby move=> ???/=; apply heval_conseq

/- Frame rule for [wp] -/

lemma hwp_frame (ht : htrm) (Q : hval -> hhProp) (H : hhProp) :
  hwp s ht Q ∗ H ==> hwp s ht (Q ∗ H) := by
  move=> ? ![> ?? -> ?];
  apply heval_conseq; apply heval_frame=> //
  ysimp=> //


/- Corollaries -/

lemma hwp_ramified :
  (hwp s ht Q) ∗ (Q -∗ Q') ==> hwp s ht Q' := by
  apply hhimpl_trans
  { apply hwp_frame }
  apply hwp_conseq
  sby srw -hqwand_equiv

lemma hwp_conseq_frame :
  Q1 ∗ H ===> Q2 →
  (hwp s t Q1) ∗ H ==> (hwp s t Q2) :=
by
  srw -hqwand_equiv
  move=> M
  apply @hhimpl_trans (h₂ := (hwp s t Q1) ∗ (Q1 -∗ Q2))
  { sby apply hhimpl_frame_r }
  apply hwp_ramified

lemma hwp_ramified_trans t H Q1 Q2 :
  H ==> (hwp s t Q1) ∗ (Q1 -∗ Q2) →
  H ==> (hwp s t Q2) :=
by
  move=> M
  ychange M
  apply hwp_ramified

lemma hwp_union (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  hwp (s₁ ∪ s₂) ht Q = hwp s₁ ht (fun hv => hwp s₂ ht (fun hv' => Q (hv ∪_s₁ hv'))) := by
    move=> ?
    apply hhimpl_antisymm=> ?<;> unfold hwp=> ?
    { sby apply heval_unfocus }
    sby apply heval_focus

@[simp]
lemma fun_insert0: (hv ∪_∅ hv') = hv' := by
  sby funext a; simp [hunion, fun_insert]

lemma hwp0_dep : hwp (∅ : Set α) ht Q = h∃ hv, Q hv := by
  apply hhimpl_antisymm=> h <;> unfold hwp
  { scase! => hQ _ /(_ (fun _ : α => val_unit)) /(_ h) H
    specialize H ?_=> //
    sby scase!: H=> hv' }
  scase! => hv /= ?; exists (fun _ _ _ => True)=> ⟨?//|? h' heq ⟨//|⟩/==⟩
  sby shave<-//: h = h'; funext x; move: (heq x)

lemma hwp0 : hwp (∅ : Set α) ht (fun _ => Q) = Q := by
  sby srw hwp0_dep; apply hhimpl_antisymm=> ?; scase!

/- ---------- Hyper Weakest-Precondition Reasoning Rules for Hyper Terms ---------- -/

lemma hwp_val v (Q : hval -> hhProp) :
  Q v ==> hwp s (trm_val ∘ v) Q :=
by sby apply htriple_val

lemma hwp_fun (x : α -> var) (ht : α -> trm) (Q : hval -> hhProp) :
  (Q fun a => val_fun (x a) (ht a)) ==> hwp s (fun a => trm_fun (x a) (ht a)) Q :=
  by sby apply htriple_fun

lemma hwp_fix (x f : α -> var) (ht : α -> trm) (Q : hval -> hhProp) :
  (Q fun a => val_fix (f a) (x a) (ht a)) ==> hwp s (fun a => trm_fix (f a) (x a) (ht a)) Q :=
  by sby apply htriple_fix

lemma hwp_if (b : α -> Bool) (ht₁ ht₂ : α -> trm) (Q : hval -> hhProp) :
  hwp s (fun a => if b a then ht₁ a else ht₂ a) Q ==> hwp s (fun a => trm_if (val_bool (b a)) (ht₁ a) (ht₂ a)) Q :=
  by sby apply htriple_if

lemma hwp_app_fun (hv₁ : hval) (x : α -> var) (ht₁ : α -> trm) (hv₂ : hval) (Q : hval -> hhProp) :
  (forall d, d ∈ s -> hv₁ d = val_fun (x d) (ht₁ d)) ->
  hwp s (fun a => subst (x a) (hv₂ a) (ht₁ a)) Q ==> hwp s (fun a => trm_app (hv₁ a) (hv₂ a)) Q :=
  by sby move=> ?; apply htriple_app_fun

lemma hwp_app_fix (hv₁ : hval) (x f : α -> var) (ht₁ : α -> trm) (hv₂ : hval) (Q : hval -> hhProp) :
  (forall d, d ∈ s -> hv₁ d = val_fix (f d) (x d) (ht₁ d)) ->
  hwp s (fun a => subst (x a) (hv₂ a) $ subst (f a) (hv₁ a) $ ht₁ a) Q ==> hwp s (fun a => trm_app (hv₁ a) (hv₂ a)) Q :=
  by sby move=> ?; apply htriple_app_fix

lemma hwp_seq (ht₁ ht₂ : htrm) (Q : hval -> hhProp) :
  hwp s ht₁ (fun _ => hwp s ht₂ Q) ==> hwp s (fun a => trm_seq (ht₁ a) (ht₂ a)) Q :=
  by sby move=> ??; apply heval_seq

lemma hwp_let (x : α -> var) (ht₁ ht₂ : htrm) (Q : hval -> hhProp) :
  hwp s ht₁ (fun v ↦ hwp s (fun a => subst (x a) (v a) (ht₂ a)) Q) ==> hwp s (fun a => trm_let (x a) (ht₁ a) (ht₂ a)) Q :=
  by sby move=> ??; apply heval_let


end HWeakestPrecondition
