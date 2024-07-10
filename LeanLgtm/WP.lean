import Ssreflect.Lang
import Mathlib.Data.Finmap
import LeanLgtm.Util

import LeanLgtm.Basic
import LeanLgtm.XSimp
import LeanLgtm.SepLog

open trm val prim

/- ---------- Definition and Structural Rules for [wp] ---------- -/

/- Definition of [wp] -/

def wp (t : trm) (Q : val → hprop) : hprop :=
  fun s ↦ eval s t Q

/- Equivalence b/w [wp] and [triple] -/

lemma wp_equiv t H Q :
  (H ==> wp t Q) ↔ triple t H Q :=
by
  sby move=> ⟨|⟩

/- Consequence rule for [wp] -/

lemma wp_conseq t Q1 Q2 :
  Q1 ===> Q2 →
  wp t Q1 ==> wp t Q2 :=
by
  move=> ??
  srw []wp => ?
  sby apply eval_conseq

/- Frame rule for [wp] -/

lemma wp_frame t H Q :
  (wp t Q) ∗ H ==> wp t (Q ∗∗ H) :=
by
  move=> h ![????? hU]
  srw hU wp
  apply eval_conseq
  { sby apply eval_frame }
  sorry

/- Corollaries -/

lemma wp_ramified t Q1 Q2 :
  (wp t Q1) ∗ (Q1 -∗∗ Q2) ==> (wp t Q2) :=
by
  apply himpl_trans
  { apply wp_frame }
  apply wp_conseq
  sorry
  -- apply qwand_cancel

lemma wp_conseq_frame t H Q1 Q2 :
  Q1 ∗∗ H ===> Q2 →
  (wp t Q1) ∗ H ==> (wp t Q2) :=
by
  srw -qwand_equiv
  move=> ?
  sorry

lemma wp_ramified_trans t H Q1 Q2 :
  H ==> (wp t Q1) ∗ (Q1 -∗∗ Q2) →
  H ==> (wp t Q2) :=
by
  move=> ?
  sorry


/- ---------- Weakest-Precondition Reasoning Rules for Terms ---------- -/

lemma wp_eval_like t1 t2 Q :
  eval_like t1 t2 →
  wp t1 Q ==> wp t2 Q :=
by
  sby move=> hEval ? /hEval

lemma wp_val v Q :
  Q v ==> wp (trm_val v) Q :=
by sdone

lemma wp_fun x t Q :
  Q (val_fun x t) ==> wp (trm_fun x t) Q :=
by sdone

lemma wp_fix f x t Q :
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q :=
by sdone

lemma wp_app_fun x v1 v2 t1 Q :
  v1 = val_fun x t1 →
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q :=
by
  move=> ? ??
  sby apply eval.eval_app_fun

lemma wp_app_fix f x v1 v2 t1 Q :
  v1 = val_fix f x t1 →
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q :=
by
  move=> ? ??
  sby apply eval.eval_app_fix

lemma wp_seq t1 t2 Q :
  wp t1 (fun _ ↦ wp t2 Q) ==> wp (trm_seq t1 t2) Q :=
by
  move=> ??
  sby apply eval.eval_seq

lemma wp_let x t1 t2 Q :
  wp t1 (fun v ↦ wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q :=
by
  move=> ??
  sby apply eval.eval_let

lemma wp_if (b : Bool) t1 t2 Q :
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q :=
by
  move=> ??
  sby apply eval.eval_if

lemma wp_if_case (b : Bool) t1 t2 Q :
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q :=
by
  apply himpl_trans (wp (if b then t1 else t2) Q)
  { sby scase_if=> ?? }
  apply wp_if


/- ======================= WP Generator ======================= -/
/- Below we define a function [wpgen t] recursively over [t] such that
   [wpgen t Q] entails [wp t Q].

   We actually define [wpgen E t], where [E] is a list of bindings, to
   compute a formula that entails [wp (isubst E t)], where [isubst E t]
   is the iterated substitution of bindings from [E] inside [t].
-/

open AList

abbrev ctx := AList (fun _ : var ↦ val)

def ctx_equiv (E1 E2 : ctx) : Prop :=
  forall x, lookup x E1 = lookup x E2

lemma lookup_app (E1 E2 : ctx) x :
  lookup x (E1 ∪ E2) = match lookup x E1 with
                        | some v => some v
                        | none   => lookup x E2 :=
by
  cases eqn:(lookup x E1)=> /=
  { srw lookup_eq_none at eqn
    sby srw lookup_union_right }
  srw lookup_union_left=>//
  sby srw -lookup_isSome

lemma lookup_ins x y v (E : ctx) :
  lookup y (insert x v E) = if x = y then some v else lookup y E :=
by
  scase_if=> ?
  { srw lookup_insert }
  srw lookup_insert_ne
  sdone

lemma lookup_rem x y (E : ctx) :
  lookup x (erase y E) = if x = y then none else lookup x E :=
by
  scase_if=> ?
  { sby srw lookup_eq_none mem_erase }
  sby srw lookup_erase_ne

lemma rem_app x (E1 E2 : ctx) :
  erase x (E1 ∪ E2) = erase x E1 ∪ erase x E2 :=
by
  apply union_erase

lemma ctx_equiv_rem x E1 E2 :
  ctx_equiv E1 E2 →
  ctx_equiv (erase x E1) (erase x E2) :=
by
  sby srw []ctx_equiv lookup_rem

lemma ctx_disjoint_rem x (E1 E2 : ctx) :
  Disjoint E1 E2 →
  Disjoint (erase x E1) (erase x E2) :=
by
  sby srw []AList.Disjoint -AList.mem_keys=> ?? /mem_erase

lemma ctx_disjoint_equiv_app (E1 E2 : ctx) :
  Disjoint E1 E2 →
  ctx_equiv (E1 ∪ E2) (E2 ∪ E1) :=
by
  move=> /[swap] x
  srw []lookup_app
  cases eqn1:(lookup x E1) <;> cases eqn2:(lookup x E2) =>//=
  srw AList.Disjoint -AList.mem_keys=> hIn
  apply False.elim ; apply hIn
  srw -lookup_isSome
  sby rw [eqn1]


/- Definition of Multi-Substitution -/

def isubst (E : ctx) (t : trm) : trm :=
  match t with
  | trm_val v =>
      v
  | trm_var x =>
      match lookup x E with
      | none   => t
      | some v => v
  | trm_fun x t1 =>
      trm_fun x (isubst (erase x E) t1)
  | trm_fix f x t1 =>
      trm_fix f x (isubst (erase x (erase f E)) t1)
  | trm_if t0 t1 t2 =>
      trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
      trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
      trm_let x (isubst E t1) (isubst (erase x E) t2)
  | trm_app t1 t2 =>
      trm_app (isubst E t1) (isubst E t2)


/- Properties of Multi-Substitution -/

/- Not sure if it's possible to prove some of the following lemmas as
   Lean does not support induction for mutually inductive types. -/

lemma isubst_nil t :
  isubst ∅ t = t :=
by
  -- induction t
  sorry

lemma subst_eq_isubst_one x v t :
  subst x v t = isubst (insert x v ∅) t :=
by
  -- induction t
  sorry

lemma isubst_ctx_equiv t E1 E2 :
  ctx_equiv E1 E2 →
  isubst E1 t = isubst E2 t :=
by
  -- induction t
  sorry

lemma isubst_app t E1 E2 :
  isubst (E1 ∪ E2) t = isubst E2 (isubst E1 t) :=
by
  --induction t
  sorry

lemma app_insert_one_r x v (l : ctx) :
  insert x v l = (insert x v ∅) ∪ l :=
by
  move=> !;
  sby srw union_entries []insert_entries empty_entries

lemma isubst_cons x v E t :
  isubst (insert x v E) t = isubst E (subst x v t) :=
by
  srw app_insert_one_r isubst_app -subst_eq_isubst_one

lemma isubst_app_swap t (E1 E2 : ctx) :
  Disjoint E1 E2 →
  isubst (E1 ∪ E2) t = isubst (E2 ∪ E1) t :=
by
  move=> ?
  apply isubst_ctx_equiv
  sby apply ctx_disjoint_equiv_app

lemma isubst_rem x v (E : ctx) t :
  isubst (insert x v E) t = subst x v (isubst (erase x E) t) :=
by
  srw subst_eq_isubst_one -isubst_app isubst_app_swap
  { apply isubst_ctx_equiv=> ?
    srw lookup_ins
    scase_if=> ?
    { srw lookup_union_left //
      srw lookup_insert }
    srw lookup_union_right
    rw [lookup_rem]
    scase_if=>//
    sby move=> /mem_insert }
  move=> ?
  sby srw Not -[]mem_keys mem_erase mem_insert => [] ?? []

lemma isubst_rem_2 f x vf vx (E : ctx) t :
  isubst (insert f vf (insert x vx E)) t =
  subst x vx (subst f vf (isubst (erase x (erase f E)) t)) :=
by
  srw !subst_eq_isubst_one -!isubst_app isubst_app_swap
  { apply isubst_ctx_equiv=> ?
    srw !lookup_ins
    scase_if=>?
    { srw !lookup_union_left //
      srw lookup_insert }
    scase_if=> ?
    { srw lookup_union_left
      rw [lookup_union_right, lookup_insert]
      srw Not at *
      rw [mem_insert]=> //
      sby srw mem_union []mem_insert }
    srw lookup_union_right
    sdo 2 rw [lookup_rem]
    scase_if=>//
    scase_if=>//
    srw Not at *
    sby srw mem_union []mem_insert => [] [] }
  move=> ?
  srw Not -[]mem_keys !mem_erase => [] ? [] ??
  sby srw mem_union []mem_insert


/- ------------------ Definition of [wpgen] ------------------ -/

/- Defining [mkstruct] -/

abbrev formula := (val → hprop) → hprop

/- [mkstruct F] transforms a formula [F] into one satisfying structural
   rules of Separation Logic. -/

def mkstruct (F : formula) :=
  fun Q ↦ h∃ Q', F Q' ∗ (Q' -∗∗ Q)

lemma mkstruct_ramified Q1 Q2 F :
  (mkstruct F Q1) ∗ (Q1 -∗∗ Q2) ==> (mkstruct F Q2) :=
by
  srw []mkstruct
  sorry --xsimp

lemma mkstruct_erase Q F :
  F Q ==> mkstruct F Q :=
by
  srw mkstruct
  sorry --xsimp

lemma mkstruct_conseq F Q1 Q2 :
  Q1 ===> Q2 →
  mkstruct F Q1 ==> mkstruct F Q2 :=
by
  srw []mkstruct => ?
  sorry --xpull

lemma mkstruct_frame F H Q :
  (mkstruct F Q) ∗ H ==> mkstruct F (Q ∗∗ H) :=
by
  srw []mkstruct
  sorry --xpull

lemma mkstruct_monotone F1 F2 Q :
  (forall Q, F1 Q ==> F2 Q) →
  mkstruct F1 Q ==> mkstruct F2 Q :=
by
  move=> ?
  srw []mkstruct
  sorry --xpull


/- Auxiliary Definitions for [wpgen] -/

def wpgen_fail : formula :=
  fun _ ↦ ⌜false⌝

def wpgen_val (v : val) : formula :=
  fun Q ↦ Q v

def wpgen_fun (Fof : val → formula) : formula :=
  fun Q ↦ h∀ vf, ⌜forall vx Q', Fof vx Q' ==>
    wp (trm_app (trm_val vf) (trm_val vx)) Q'⌝ -∗ Q vf

def wpgen_fix (Fof : val → val → formula) : formula :=
  fun Q ↦ h∀ vf, ⌜forall vx Q', Fof vf vx Q' ==>
    wp (trm_app vf vx) Q'⌝ -∗ Q vf

def wpgen_var (E : ctx) (x : var) : formula :=
  match lookup x E with
  | none   => wpgen_fail
  | some v => wpgen_val v

def wpgen_seq (F1 F2 : formula) : formula :=
  fun Q ↦ F1 (fun _ ↦ F2 Q)

def wpgen_let (F1 : formula) (F2of : val → formula) : formula :=
  fun Q ↦ F1 (fun v ↦ F2of v Q)

def wpgen_if (t : trm) (F1 F2 : formula) : formula :=
  fun Q ↦ h∃ (b : Bool),
    ⌜t = trm_val (val_bool b)⌝ ∗ (if b then F1 Q else F2 Q)

def wpgen_if_trm (F0 F1 F2 : formula) : formula :=
  wpgen_let F0 (fun v ↦ mkstruct (wpgen_if v F1 F2))

def wpgen_app (t : trm) : formula :=
  fun Q ↦ h∃ H, H ∗ ⌜triple t H Q⌝


/- Recursive Definition of [wpgen] -/

def wpgen (E : ctx) (t : trm) : formula :=
  mkstruct (match t with
  | trm_val v       => wpgen_val v
  | trm_var x       => wpgen_var E x
  | trm_fun x t1    => wpgen_fun (fun v ↦ wpgen (insert x v E) t1)
  | trm_fix f x t1  => wpgen_fix
      (fun vf v ↦ wpgen (insert f vf (insert x v E)) t1)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  | trm_seq t1 t2   => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v ↦ wpgen (insert x v E) t2)
  | trm_app _ _   => wpgen_app (isubst E t) )


/- ---------------- Soundness of [wpgen] ---------------- -/

def formula_sound (t : trm) (F : formula) : Prop :=
  forall Q, F Q ==> wp t Q

lemma wp_sound t :
  formula_sound t (wp t) :=
by
  sby move=> ??

/- Soundness lemma for [mkstruct] -/

lemma mkstruct_wp t :
  mkstruct (wp t) = wp t :=
by
  move=> ! ?
  apply himpl_antisym
  { srw mkstruct
    sorry /- xpull -/ }
  apply mkstruct_erase

lemma mkstruct_sound t F :
  formula_sound t F →
  formula_sound t (mkstruct F) :=
by
  srw []formula_sound => ? ?
  srw -mkstruct_wp
  sby apply mkstruct_monotone=> ??

/- Soundness lemmas for each term construct -/

lemma wpgen_fail_sound t :
  formula_sound t wpgen_fail :=
by
  move=> ?
  srw wpgen_fail
  sorry --xpull

lemma wpgen_val_sound v :
  formula_sound (trm_val v) (wpgen_val v) :=
by
  move=> ?
  srw wpgen_val
  apply wp_val

lemma wpgen_fun_sound x t1 Fof :
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) →
  formula_sound (trm_fun x t1) (wpgen_fun Fof) :=
by
  move=> ? ?
  srw wpgen_fun
  apply (himpl_hforall_l _ (val_fun x t1))
  sorry -- xchange hwand_hpure_l

lemma wpgen_fix_sound f x t1 Fof :
  (forall vf vx, formula_sound (subst v vx (subst f vf t1)) (Fof vf vx)) →
  formula_sound (trm_fix f x t1) (wpgen_fix Fof) :=
by
  move=> ? ?
  srw wpgen_fix
  apply (himpl_hforall_l _ (val_fix f x t1))
  sorry -- xchange hwand_hpure_l

lemma wpgen_seq_sound F1 F2 t1 t2 :
  formula_sound t1 F1 →
  formula_sound t2 F2 →
  formula_sound (trm_seq t1 t2) (wpgen_seq F1 F2) :=
by
  srw []formula_sound => ?? Q
  srw wpgen_seq
  apply (himpl_trans (wp t1 (fun _ ↦ wp t2 Q)))
  { apply (himpl_trans (wp t1 fun _ ↦ F2 Q))
    move=> ? //
    apply wp_conseq => ? /=
    sdone }
  apply wp_seq

lemma wpgen_let_sound F1 F2of x t1 t2 :
  formula_sound t1 F1 →
  (forall v, formula_sound (subst x v t2) (F2of v)) →
  formula_sound (trm_let x t1 t2) (wpgen_let F1 F2of) :=
by
  srw []formula_sound => ?? Q
  srw wpgen_let
  apply himpl_trans (wp t1 (fun v ↦ wp (subst x v t2) Q))
  { apply himpl_trans (wp t1 (fun v ↦ F2of v Q ))
    {  sby move=> ? }
    apply wp_conseq => ? /=
    sdone }
  apply wp_let

lemma wpgen_if_sound F1 F2 t0 t1 t2 :
  formula_sound t1 F1 →
  formula_sound t2 F2 →
  formula_sound (trm_if t0 t1 t2) (wpgen_if t0 F1 F2) :=
by
  srw []formula_sound => ?? Q
  srw wpgen_if
  sorry -- xpull

lemma wpgen_app_sound t :
  formula_sound t (wpgen_app t) :=
by
 move=> ??
 srw wpgen_app
 sorry -- xpull

/- Main soundness lemma -/

lemma wpgen_sound E t :
  formula_sound (isubst E t) (wpgen E t) :=
by
  -- elim: t
  scase: t
  any_goals move=> * ; srw isubst wpgen ; try apply mkstruct_sound
  { apply wpgen_val_sound }
  { srw wpgen_var
    cases eqn:(lookup _ E)=> /=
    { apply wpgen_fail_sound }
    apply wpgen_val_sound }
  { apply wpgen_fun_sound=> ?
    srw -isubst_rem
    sorry /- need induction -/ }
  { apply wpgen_fix_sound=> *
    srw -isubst_rem_2
    sorry }
  { srw isubst
    apply wpgen_app_sound }
  { apply wpgen_seq_sound
    sorry ; sorry }
  { apply wpgen_let_sound
    sorry
    move=> ?
    srw -isubst_rem
    sorry }
  { apply wpgen_if_sound
    sorry ; sorry }

lemma himpl_wpgen_wp t Q :
  wpgen ∅ t Q ==> wp t Q :=
by
  move=> ? /wpgen_sound
  sby srw isubst_nil

lemma triple_of_wpgen t H Q :
  H ==> wpgen ∅ t Q →
  triple t H Q :=
by
  srw -wp_equiv=> ?
  sorry -- xchange
