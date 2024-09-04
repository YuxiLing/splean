import Lean

-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.XChange
import Lgtm.Unary.SepLog
import Lgtm.Unary.WPUtil

open trm val prim

namespace Unary

local instance : Coe val trm where
  coe v := trm.trm_val v

/- ---------- Definition and Structural Rules for [wp] ---------- -/

/- Definition of [wp] -/

def wp (t : trm) (Q : val → hProp) : hProp :=
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
  (wp t Q) ∗ H ==> wp t (Q ∗ H) :=
by
  move=> h ![????? hU]
  srw hU wp
  apply eval_conseq
  { sby apply eval_frame }
  sby srw ?qstarE ; xsimp ; xsimp


/- Corollaries -/

lemma wp_ramified t (Q1 Q2 : val -> hProp) :
  (wp t Q1) ∗ (Q1 -∗ Q2) ==> (wp t Q2) :=
by
  apply himpl_trans
  { apply wp_frame }
  apply wp_conseq
  apply qwand_cancel

lemma wp_conseq_frame t H (Q1 Q2 : val -> hProp) :
  Q1 ∗ H ===> Q2 →
  (wp t Q1) ∗ H ==> (wp t Q2) :=
by
  srw -qwand_equiv
  move=> M
  apply himpl_trans ((wp t Q1) ∗ (Q1 -∗ Q2))
  { sby apply himpl_frame_r }
  apply wp_ramified


lemma wp_ramified_trans t H Q1 Q2 :
  H ==> (wp t Q1) ∗ (Q1 -∗ Q2) →
  H ==> (wp t Q2) :=
by
  move=> M
  xchange M
  apply wp_ramified


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

-- open AList

-- abbrev ctx := AList (fun _ : var ↦ val)

-- def ctx_equiv (E1 E2 : ctx) : Prop :=
--   forall x, lookup x E1 = lookup x E2

-- lemma lookup_app (E1 E2 : ctx) x :
--   lookup x (E1 ∪ E2) = match lookup x E1 with
--                         | some v => some v
--                         | none   => lookup x E2 :=
-- by
--   cases eqn:(lookup x E1)=> /=
--   { srw lookup_eq_none at eqn
--     sby srw lookup_union_right }
--   srw lookup_union_left=>//
--   sby srw -lookup_isSome

-- lemma lookup_ins x y v (E : ctx) :
--   lookup y (insert x v E) = if x = y then some v else lookup y E :=
-- by
--   scase_if=> ?
--   { srw lookup_insert }
--   srw lookup_insert_ne
--   sdone

-- lemma lookup_rem x y (E : ctx) :
--   lookup x (erase y E) = if x = y then none else lookup x E :=
-- by
--   scase_if=> ?
--   { sby srw lookup_eq_none mem_erase }
--   sby srw lookup_erase_ne

-- lemma rem_app x (E1 E2 : ctx) :
--   erase x (E1 ∪ E2) = erase x E1 ∪ erase x E2 :=
-- by
--   apply union_erase

-- lemma ctx_equiv_rem x E1 E2 :
--   ctx_equiv E1 E2 →
--   ctx_equiv (erase x E1) (erase x E2) :=
-- by
--   sby srw []ctx_equiv lookup_rem

-- lemma ctx_disjoint_rem x (E1 E2 : ctx) :
--   Disjoint E1 E2 →
--   Disjoint (erase x E1) (erase x E2) :=
-- by
--   sby srw []AList.Disjoint -AList.mem_keys=> ?? /mem_erase

-- lemma ctx_disjoint_equiv_app (E1 E2 : ctx) :
--   Disjoint E1 E2 →
--   ctx_equiv (E1 ∪ E2) (E2 ∪ E1) :=
-- by
--   move=> /[swap] x
--   srw []lookup_app
--   cases eqn1:(lookup x E1) <;> cases eqn2:(lookup x E2) =>//=
--   srw AList.Disjoint -AList.mem_keys=> hIn
--   apply False.elim ; apply hIn
--   srw -lookup_isSome
--   sby rw [eqn1]


-- /- Definition of Multi-Substitution -/

-- def isubst (E : ctx) (t : trm) : trm :=
--   match t with
--   | trm_val v =>
--       v
--   | trm_var x =>
--       match lookup x E with
--       | none   => t
--       | some v => v
--   | trm_fun x t1 =>
--       trm_fun x (isubst (erase x E) t1)
--   | trm_fix f x t1 =>
--       trm_fix f x (isubst (erase x (erase f E)) t1)
--   | trm_if t0 t1 t2 =>
--       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
--   | trm_seq t1 t2 =>
--       trm_seq (isubst E t1) (isubst E t2)
--   | trm_let x t1 t2 =>
--       trm_let x (isubst E t1) (isubst (erase x E) t2)
--   | trm_app t1 t2 =>
--       trm_app (isubst E t1) (isubst E t2)


-- /- Properties of Multi-Substitution -/

-- /- Not sure if it's possible to prove some of the following lemmas as
--    Lean does not support induction for mutually inductive types. -/

-- lemma isubst_nil t :
--   isubst ∅ t = t :=
-- by
--   -- induction t
--   sorry

-- lemma subst_eq_isubst_one x v t :
--   subst x v t = isubst (insert x v ∅) t :=
-- by
--   -- induction t
--   sorry

-- lemma isubst_ctx_equiv t E1 E2 :
--   ctx_equiv E1 E2 →
--   isubst E1 t = isubst E2 t :=
-- by
--   -- induction t
--   sorry

-- lemma isubst_app t E1 E2 :
--   isubst (E1 ∪ E2) t = isubst E2 (isubst E1 t) :=
-- by
--   --induction t
--   sorry

-- lemma app_insert_one_r x v (l : ctx) :
--   insert x v l = (insert x v ∅) ∪ l :=
-- by
--   move=> !;
--   sby srw union_entries []insert_entries empty_entries

-- lemma isubst_cons x v E t :
--   isubst (insert x v E) t = isubst E (subst x v t) :=
-- by
--   srw app_insert_one_r isubst_app -subst_eq_isubst_one

-- lemma isubst_app_swap t (E1 E2 : ctx) :
--   Disjoint E1 E2 →
--   isubst (E1 ∪ E2) t = isubst (E2 ∪ E1) t :=
-- by
--   move=> ?
--   apply isubst_ctx_equiv
--   sby apply ctx_disjoint_equiv_app

-- lemma isubst_rem x v (E : ctx) t :
--   isubst (insert x v E) t = subst x v (isubst (erase x E) t) :=
-- by
--   srw subst_eq_isubst_one -isubst_app isubst_app_swap
--   { apply isubst_ctx_equiv=> ?
--     srw lookup_ins
--     scase_if=> ?
--     { srw lookup_union_left //
--       srw lookup_insert }
--     srw lookup_union_right
--     rw [lookup_rem]
--     scase_if=>//
--     sby move=> /mem_insert }
--   move=> ?
--   sby srw Not -[]mem_keys mem_erase mem_insert => [] ?? []

-- lemma isubst_rem_2 f x vf vx (E : ctx) t :
--   isubst (insert f vf (insert x vx E)) t =
--   subst x vx (subst f vf (isubst (erase x (erase f E)) t)) :=
-- by
--   srw !subst_eq_isubst_one -!isubst_app isubst_app_swap
--   { apply isubst_ctx_equiv=> ?
--     srw !lookup_ins
--     scase_if=>?
--     { srw !lookup_union_left //
--       srw lookup_insert }
--     scase_if=> ?
--     { srw lookup_union_left
--       rw [lookup_union_right, lookup_insert]
--       srw Not at *
--       rw [mem_insert]=> //
--       sby srw mem_union []mem_insert }
--     srw lookup_union_right
--     sdo 2 rw [lookup_rem]
--     scase_if=>//
--     scase_if=>//
--     srw Not at *
--     sby srw mem_union []mem_insert => [] [] }
--   move=> ?
--   srw Not -[]mem_keys !mem_erase => [] ? [] ??
--   sby srw mem_union []mem_insert


/- ------------------ Definition of [wpgen] ------------------ -/

/- Defining [mkstruct] -/

abbrev formula := (val → hProp) → hProp

/- [mkstruct F] transforms a formula [F] into one satisfying structural
   rules of Separation Logic. -/

def mkstruct (F : formula) :=
  fun (Q : val -> hProp) ↦ ∃ʰ Q', F Q' ∗ (Q' -∗ Q)

def structural (F : formula) :=
  forall Q, mkstruct F Q ==> F Q

def structural_pred (S : α -> formula) :=
  ∀ x, structural $ S x


lemma mkstruct_ramified Q1 Q2 F :
  (mkstruct F Q1) ∗ (Q1 -∗ Q2) ==> (mkstruct F Q2) :=
by
  srw []mkstruct
  xsimp

lemma mkstruct_erase Q F :
  F Q ==> mkstruct F Q :=
by
  srw mkstruct ; xsimp

lemma mkstruct_conseq F Q1 Q2 :
  Q1 ===> Q2 →
  mkstruct F Q1 ==> mkstruct F Q2 :=
by
  srw []mkstruct => h
  xpull=> ?
  unfold qimpl at *
  xsimp
  sdone

lemma mkstruct_frame F H Q :
  (mkstruct F Q) ∗ H ==> mkstruct F (Q ∗ H) :=
by
  srw []mkstruct
  xpull=> ?
  xsimp

lemma mkstruct_monotone F1 F2 Q :
  (forall Q, F1 Q ==> F2 Q) →
  mkstruct F1 Q ==> mkstruct F2 Q :=
by
  move=> ?
  srw []mkstruct
  xpull=> ?
  xsimp
  sdone


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

-- def wpgen_var (E : ctx) (x : var) : formula :=
--   match lookup x E with
--   | none   => wpgen_fail
--   | some v => wpgen_val v

def wpgen_seq (F1 F2 : formula) : formula :=
  fun Q ↦ F1 (fun _ ↦ F2 Q)

def wpgen_let (F1 : formula) (F2of : val → formula) : formula :=
  fun Q ↦ F1 (fun v ↦ F2of v Q)

def wpgen_if (t : trm) (F1 F2 : formula) : formula :=
  fun Q ↦ ∃ʰ (b : Bool),
    ⌜t = trm_val (val_bool b)⌝ ∗ (if b then F1 Q else F2 Q)

def wpgen_if_trm (F0 F1 F2 : formula) : formula :=
  wpgen_let F0 (fun v ↦ mkstruct (wpgen_if v F1 F2))

@[simp]
def wpgen_app (t : trm) : formula :=
  fun Q ↦ ∃ʰ H, H ∗ ⌜triple t H Q⌝

def wpgen_for (v₁ v₂ : trm) (F1 : val -> formula) : formula :=
  mkstruct fun Q =>
    ∃ʰ n₁ n₂ : Int, ⌜v₁ = n₁⌝ ∗ ⌜v₂ = n₂⌝ ∗
      h∀ (S : Int -> formula),
        (let F i :=
          if i < n₂ then
            wpgen_seq (F1 (val_int i)) (S (i + 1))
          else wpgen_val val_unit
        ⌜structural_pred S /\ ∀ i, F i ===> S i⌝ -∗ S n₁ Q )

def wpgen_while (F1 F2 : formula) : formula := mkstruct fun Q =>
  h∀ R : formula,
    let F := wpgen_if_trm F1 (wpgen_seq F2 R) (wpgen_val val_unit)
    ⌜structural R ∧ F ===> R⌝ -∗ R Q

/- Recursive Definition of [wpgen] -/

def wpgen (t : trm) : formula :=
  mkstruct (match t with
  | trm_val v          => wpgen_val v
  | trm_fun x t1       => wpgen_fun (fun v ↦ wp $ subst x v t1)
  | trm_fix f x t1     => wpgen_fix
      (fun vf v => wp $ subst x v $ subst f vf t1)
  | trm_if t0 t1 t2    => wpgen_if t0 (wp t1) (wp t2)
  | trm_seq t1 t2      => wpgen_seq (wp t1) (wp t2)
  | trm_let x t1 t2    => wpgen_let (wp t1) (fun v ↦ wp $ subst x v t2)
  | trm_app _ _        => wpgen_app t
  | trm_for x v1 v2 t1 => wpgen_for v1 v2 (fun v ↦ wp $ subst x v t1)
  | trm_while t0 t1    => wpgen_while (wp t0) (wp t1)
  | _ => wp t
  )


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
    xpull=> ?
    apply wp_ramified }
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
  xpull=> //

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
  xpull=> >
  apply himpl_trans (wp (trm_if b t1 t2) Q)=> //
  unfold wp at *
  scase: b=> /== ??
  all_goals sby apply eval.eval_if

lemma wpgen_app_sound t :
  formula_sound t (wpgen_app t) :=
by
 move=> ?
 srw wpgen_app
 xpull=> >?
 sby srw wp_equiv

lemma qimpl_wp_of_triple t F :
  (forall Q, triple t (F Q) Q) →
  F ===> wp t := by sdone

lemma triple_for_raw (x:var) (n1 n2: Int) t3 H (Q:val->hProp) :
  triple (
    if (n1 < n2)
      then (trm_seq (subst x n1 t3) (trm_for x (val_int $ n1+1) n2 t3))
      else val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q := by
  unfold triple=> ?>?
  sby constructor

lemma triple_mkstruct_pre : forall t (F:formula) Q,
  (forall Q, triple t (F Q) Q) ->
  triple t (mkstruct F Q) Q := by sorry

-- set_option pp.notation false

lemma wpgen_for_sound x v1 v2 F1 :
  (forall v, formula_sound (subst x v t1) (F1 v)) →
  formula_sound (trm_for x v1 v2 t1) (wpgen_for v1 v2 F1) := by
  move=> M
  apply qimpl_wp_of_triple=> Q
  apply triple_mkstruct_pre=> {}Q
  srw -wp_equiv
  xsimp=> >
  let S (i : Int) := wp (trm_for x i n₂ t1)
  srw wp_equiv
  apply triple_hforall _ _ S
  apply triple_hwand_hpure_l
  { sorry }
  sorry


/- Main soundness lemma -/

lemma wpgen_sound t :
  formula_sound t (wpgen t) :=
by sorry
  -- elim: t
  -- scase: t
  -- any_goals move=> * ; srw wpgen ; try apply mkstruct_sound
  -- { apply wpgen_val_sound }
  -- { srw wpgen_var
  --   cases eqn:(lookup _ E)=> /=
  --   { apply wpgen_fail_sound }
  --   apply wpgen_val_sound }
  -- { apply wpgen_fun_sound=> ?
  --   srw -isubst_rem
  --   sorry /- need induction -/ }
  -- { apply wpgen_fix_sound=> *
  --   srw -isubst_rem_2
  --   sorry }
  -- { srw isubst
  --   apply wpgen_app_sound }
  -- { apply wpgen_seq_sound
  --   sorry ; sorry }
  -- { apply wpgen_let_sound
  --   sorry
  --   move=> ?
  --   srw -isubst_rem
  --   sorry }
  -- { apply wpgen_if_sound
  --   sorry ; sorry }

lemma himpl_wpgen_wp t Q :
  wpgen t Q ==> wp t Q :=
by
  sby move=> ? /wpgen_sound

lemma triple_of_wpgen t H Q :
  H ==> wpgen t Q →
  triple t H Q :=
by
  srw -wp_equiv=> h
  xchange h
  apply himpl_wpgen_wp


/- ################################################################# -/
/-* * Practical Proofs -/

/-* This last section shows the techniques involved in setting up the lemmas
    and tactics required to carry out verification in practice, through
    concise proof scripts. -/

/- ================================================================= -/
/-* ** Lemmas for Tactics to Manipulate [wpgen] Formulae -/

lemma xstruct_lemma F H Q :
  H ==> F Q →
  H ==> mkstruct F Q := by
  move=> h
  xchange h
  unfold mkstruct
  xsimp

lemma xval_lemma v H Q :
  H ==> Q v →
  H ==> wpgen_val v Q := by
  move=> h
  xchange h

lemma xlet_lemma H F1 F2of Q :
  H ==> F1 (fun v => F2of v Q) →
  H ==> wpgen_let F1 F2of Q :=
by
  move=> h
  xchange h

lemma xseq_lemma H F1 F2 Q :
  H ==> F1 (fun _ => F2 Q) →
  H ==> wpgen_seq F1 F2 Q :=
by
  move=> h
  xchange h

lemma xif_lemma b H F1 F2 Q :
  (b = true -> H ==> F1 Q) →
  (b = false -> H ==> F2 Q) →
  H ==> wpgen_if b F1 F2 Q :=
by
  scase: b
  move=> /== h
  sby all_goals xchange h ; unfold wpgen_if ; xsimp

lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 ∗ (Q1 -∗ protect Q) ->
  H ==> wpgen_app t Q :=
by
  move=> T M
  unfold wpgen_app=> ?????
  xsimp
  apply triple_ramified_frame=> //

lemma xfun_spec_lemma (S:val->Prop) H Q Fof :
  (forall (vf : val),
    (forall (vx : val) H' Q', (H' ==> Fof vx Q') → triple (trm_app vf vx) H' Q') →
    S vf) →
  (forall vf, S vf -> (H ==> Q vf)) →
  H ==> wpgen_fun Fof Q :=
by
  move=> h1 h2
  unfold wpgen_fun
  xsimp=> ?
  apply h2 ; apply h1=> > K
  srw -wp_equiv ; xchange K
  sdone

lemma xfun_nospec_lemma  H Q Fof :
(forall (vf : val),
    (forall (vx : val) H' Q', (H' ==> Fof vx Q') → triple (trm_app vf vx) H' Q') →
    (H ==> Q vf)) →
H ==> wpgen_fun Fof Q :=
by
  move=> M
  unfold wpgen_fun
  xsimp=> ?
  apply M=>  > K
  srw -wp_equiv
  xchange K
  sdone

lemma xwp_lemma_fun v1 v2 x t H Q :
  v1 = val_fun x t →
  H ==> wpgen (subst x v2 t) Q →
  triple (trm_app v1 v2) H Q :=
by sorry

lemma xwp_lemma_fix : forall v1 v2 f x t H Q,
  v1 = val_fix f x t ->
  f != x ->
  H ==> wpgen (subst x v2 $ subst f v1 $ t) Q ->
  triple (trm_app v1 v2) H Q :=
by sorry

lemma xtriple_lemma t H (Q:val → hProp) :
  H ==> mkstruct (wpgen_app t) Q →
  triple t H Q :=
by
  move=> M
  srw -wp_equiv
  xchange M
  unfold mkstruct wpgen_app
  xpull=> >
  srw -wp_equiv => N
  xchange N
  apply wp_ramified
  -- -- fix here!
  -- xsimp
  -- rev_pure


/- ================================================================= -/
/-* ** Tactics to Manipulate [wpgen] Formulae -/

/-* The tactic are presented in chapter [WPgen]. -/

/- [xstruct] removes the leading [mkstruct]. -/

section tactics

open Lean Elab Tactic

macro "xstruct" : tactic => do
  `(tactic| apply xstruct_lemma)


set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xstruct_if_needed" : tactic => do
  match <- getGoalStxAll with
  | `($_ ==> mkstruct $_ $_) => {| apply xstruct_lemma |}
  | _ => pure ( )

macro "xval" : tactic => do
  `(tactic| (xstruct_if_needed; apply xval_lemma))

macro "xlet" : tactic => do
  `(tactic| (xstruct_if_needed; apply xlet_lemma; dsimp))

macro "xseq" : tactic => do
  `(tactic| (xstruct_if_needed; apply xseq_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xseq_xlet_if_needed" : tactic => do
  match <- getGoalStxAll with
  | `($_ ==> mkstruct $f $_) =>
    match f with
    | `(wpgen_seq $_ $_) => {| xseq |}
    | `(wpgen_let $_ $_) => {| xlet |}
    | _ => pure ( )
  | _ => pure ( )


macro "xif" : tactic => do
  `(tactic|
  (xseq_xlet_if_needed; xstruct_if_needed; apply xif_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xapp_try_clear_unit_result" : tactic => do
  let .some (_, _) := (← Lean.Elab.Tactic.getMainTarget).arrow? | pure ( )
  -- let_expr val := val | pure ()
  {| move=> _ |}

macro "xtriple" :tactic =>
  `(tactic| (intros; apply xtriple_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xwp_equiv" :tactic => do
  let_expr himpl _ wp := (<- getMainTarget) | pure ( )
  let_expr wp _ _ := wp | pure ( )
  {| rw [wp_equiv] |}


set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xtriple_if_needed" : tactic => do
  let_expr triple _ _ _ := (<- getMainTarget) | pure ( )
  {| xtriple |}

lemma xapp_simpl_lemma (F : formula) :
  H ==> F Q ->
  H ==> F Q ∗ (Q -∗ protect Q) := by sorry

elab "xsimp_step_no_cancel" : tactic => do
  let xsimp <- XSimpRIni
  /- TODO: optimise.
    Sometimes we tell that some transitions are not availible at the moment.
    So it might be possible to come up with something better than trying all
    transitions one by one -/
  withMainContext do
    xsimp_step_l  xsimp false <|>
    xsimp_step_r  xsimp <|>
    xsimp_step_lr xsimp

macro "xsimp_no_cancel_wand" : tactic =>
  `(tactic| (
    xsimp_start
    repeat' xsimp_step_no_cancel
    try rev_pure
    try hsimp
  ))

section xapp

macro "xapp_simp" : tactic => do
  `(tactic|
      first | apply xapp_simpl_lemma; try hsimp
            | xsimp_no_cancel_wand; try unfold protect; xapp_try_clear_unit_result)

macro "xapp_pre" : tactic => do
  `(tactic|
    (xseq_xlet_if_needed
     xwp_equiv
     xtriple_if_needed
     xstruct_if_needed))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
elab "xapp_try_subst" : tactic => do
  {| (unhygienic (skip=>>)
      move=>->) |}

macro "xapp_debug" :tactic => do
  `(tactic|
    (xapp_pre
     eapply xapp_lemma))

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in

elab "xapp_pick" e:term ? : tactic => do
  let thm <- (match e with
    | .none => pickTripleLemma
    | .some thm => return thm.raw.getId : TacticM Name)
  {| eapply $(mkIdent thm) |}

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
-- elab "xapp_nosubst"  : tactic => do
--   {| (xapp_pre
--       eapply xapp_lemma; xapp_pick_debug
--       rotate_left; xapp_simp=>//) |}

macro "xapp_nosubst" e:term ? : tactic =>
  `(tactic|
    (xapp_pre
     eapply xapp_lemma; xapp_pick $(e)?
     rotate_right; xapp_simp; hide_mvars=>//))

macro "xapp" : tactic =>
  `(tactic|
    (xapp_nosubst;
     try xapp_try_subst
     first
       | done
       | all_goals try srw wp_equiv
         all_goals try subst_vars))

elab "xapp" colGt e:term ? : tactic => do
  {|
    (xapp_nosubst $(e)?;
     try xapp_try_subst
     first
       | done
       | all_goals try srw wp_equiv
         all_goals try subst_vars) |}

end xapp

macro "xwp" : tactic =>
  `(tactic|
    (intros
     first | apply xwp_lemma_fix; rfl
           | apply xwp_lemma_fun; rfl))


end tactics

@[simp]
abbrev var_funs (xs:List var) (n:Nat) : Prop :=
     xs.Nodup
  /\ xs.length = n
  /\ xs != []

@[simp]
def trms_vals (vs : List var) : List trm :=
  vs.map trm_var

instance : Coe (List var) (List trm) where
  coe := trms_vals

-- lemma trms_vals_nil :
--   trms_vals .nil = .nil := by rfl
@[simp]
def trms_to_vals (ts:List trm) : Option (List val) := do
  match ts with
  | [] => return []
  | (trm_val v) :: ts' => v :: (<- trms_to_vals ts')
  | _ => failure

/- ======================= WP Generator ======================= -/
/- Below we define a function [wpgen t] recursively over [t] such that
   [wpgen t Q] entails [wp t Q].

   We actually define [wpgen E t], where [E] is a list of bindings, to
   compute a formula that entails [wp (isubst E t)], where [isubst E t]
   is the iterated substitution of bindings from [E] inside [t].
-/

open AList

abbrev ctx := AList (fun _ : var ↦ val)

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
  | trm_for x n1 n2 t =>
      trm_for x (isubst E n1) (isubst E n2) (isubst (erase x E) t)
  | trm_while c t =>
      trm_while (isubst E c) (isubst E t)


def _root_.List.mkAlist [DecidableEq α] (xs : List α) (vs : List β) :=
  ((xs.zip vs).map fun (x, y) => ⟨x, y⟩).toAList

lemma trm_apps1 :
  trm_app t1 t2 = trm_apps t1 [t2] := by rfl

lemma trm_apps2 :
  trm_apps (trm_app t1 t2) ts = trm_apps t1 (t2::ts) := by rfl


lemma xwp_lemma_funs (xs : List _) (vs : List val) :
  t = trm_apps v0 ts ->
  v0 = val_funs xs t1 ->
  trms_to_vals ts = vs ->
  var_funs xs vs.length ->
  H ==> wpgen (isubst (xs.mkAlist vs) t1) Q ->
  triple t H Q := by sorry

lemma xwp_lemma_fixs (xs : List _) (v0 : val) (vs : List val) :
  t = trm_apps v0 ts ->
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = vs ->
  var_funs xs vs.length ->
  f ∉ xs ->
  H ==> wpgen (isubst ((f :: xs).mkAlist (v0 :: vs)) t1) Q ->
  triple t H Q := by sorry

lemma wp_of_wpgen :
  H ==> wpgen t Q →
  H ==> wp t Q := by sorry


macro "xwp" : tactic =>
  `(tactic|
    (intros
     try srw trm_apps1
     srw ?trm_apps2
     first | (apply xwp_lemma_fixs; rfl; rfl; sdone; sdone; sdone)=> //
           | (apply xwp_lemma_funs; rfl; rfl; rfl; sdone)=> //
           | apply wp_of_wpgen
     all_goals try simp [wpgen, subst, isubst, subst, trm_apps, AList.lookup, List.dlookup]))

end Unary

open Unary

macro "lang_def" n:ident ":=" l:lang : command => do
  `(def $n:ident : val := [lang| $l])

local instance : HAdd ℤ ℤ val := ⟨fun x y => val.val_int (x + y)⟩
local instance : HAdd ℤ ℕ val := ⟨fun x y => (x + (y : Int))⟩
local instance : HAdd ℕ ℤ val := ⟨fun x y => ((x : Int) + y)⟩

syntax ppGroup("{ " term " }") ppSpace ppGroup("[" lang "]") ppSpace ppGroup("{ " Lean.Parser.Term.funBinder ", " term " }") : term
syntax ppGroup("{ " term " }") ppSpace ppGroup("[" lang "]") ppSpace ppGroup("{ " term " }") : term

macro_rules
  | `({ $P }[$t:lang]{$v, $Q}) => `(triple [lang| $t] $P (fun $v => $Q))
  | `({ $P }[$t:lang]{$Q}) => `(triple [lang| $t] $P (fun _ => $Q))

@[app_unexpander triple] def unexpandTriple : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $t] $P fun $v ↦ $Q) => `({ $P }[$t:lang]{$v, $Q})
  | _ => throw ( )

elab "xsimpr" : tactic => do
  xsimp_step_r (<- XSimpRIni)

/- For loop -/

set_option linter.hashCommand false

@[simp]
lemma oneE : OfNat.ofNat 1 = 1 := by rfl

lemma xfor_inv_lemma (I : Int -> hProp) (a b : Int)
  (F : val -> formula)
  (Q : val -> hProp) :
  structural_pred F ->
  a <= b ->
    (∃ H',
      H ==> I a ∗ H' ∧
      (∀ i, a <= i ∧ i < b -> I i ==> F i fun _ => I (i + 1)) ∧
      (fun _ => I b ∗ H') ===> Q) ->
    H ==> wpgen_for a b F Q := by
  move=> sF L ![H' Ma Mb Mc]
  unfold wpgen_for
  apply himpl_trans; rotate_left; apply mkstruct_erase
  unfold_let
  xsimp[a,b]=> //== ls
  srw OfNat.ofNat instOfNat instOfNatNat /== => hs
  -- shave-> ls hs: i + (OfNat.ofNat 1) = i + 1; sdone
  shave P: ∀ i, a <= i ∧ i <= b -> I i ==> S i fun _ => I b
  { move=> i [/[swap] iLb]
    apply (Int.le_induction_down _ _ _ iLb)
    { move=> ?
      xchange (hs b)=> /==
      sby xval }
    move=> i ? ih ?
    xchange hs
    scase_if=> // ?; rotate_left; omega
    xseq
    xchange Mb;
    srw OfNat.ofNat instOfNat instOfNatNat /==
    omega
    apply himpl_trans; rotate_left; apply sF
    unfold mkstruct; xsimp; apply ih; omega }
  xchange Ma; xchange P; omega
  apply himpl_trans; rotate_left; apply ls
  unfold mkstruct; xsimp; apply Mc

lemma wp_structural : structural (wp t) := by
  move=> Q; unfold mkstruct
  xsimp=> >; apply wp_ramified
#hint_xapp triple_get
#hint_xapp triple_set
#hint_xapp triple_add
#hint_xapp triple_ref
#hint_xapp triple_free


elab "xseq_xlet_if_needed_xwp" : tactic => do
  match <- getGoalStxAll with
  | `($_ ==> mkstruct $f $_) =>
    match f with
    | `(wpgen_seq $_ $_) => {| xseq; xwp |}
    | `(wpgen_let $_ $_) => {| xlet; xwp |}
    | _ => pure ( )
  | _ => pure ( )

open Lean.Elab.Tactic in

elab "⟨" ts:tactic,* "⟩" : tactic => do
  let l := (<- getUnsolvedGoals).length
  let tl := ts.getElems.size
  if tl != l then
    throwError "invalid number of goals, expectded {l}, got {tl}"
  idxGoal fun i => evalTactic ts.getElems[i]!

-- example : True /\ 5=5 /\ False /\ (True -> False) := by
--   (repeat' apply And.intro); ⟨ trivial, rfl, skip, move=> ? ⟩


macro "xfor" I:term : tactic => do
  `(tactic| (
    xwp
    xseq_xlet_if_needed_xwp
    xstruct_if_needed
    apply xfor_inv_lemma $I
    ⟨(move=> ?; apply wp_structural), try omega, (
      constructor; (repeat' apply And.intro)
      all_goals (try xsimp)
      all_goals (try srw wp_equiv)
    )⟩
    ))

/- While loop -/

lemma xwhile_inv_lemma (I : Bool -> α -> hProp)
  (F1 F2 : formula) :
    WellFounded R ->
    (H ==> ∃ʰ b a, I b a) ->
    (∀ (S: formula) b X, structural S ->
        (∀ b a', R a' X -> (I b a') ==> S fun _ => ∃ʰ a, I false a) ->
        I b X ==> wpgen_if_trm F1 (wpgen_seq F2 S) (wpgen_val val_unit) fun _ => ∃ʰ a, I false a) ->
    H ==> wpgen_while F1 F2 (fun _ => ∃ʰ a, I false a) := by

  move=> wf hh hs; xchange hh=> >
  unfold wpgen_while; xchange mkstruct_erase=> [rs fs]
  xsimp; move: b
  apply WellFounded.induction wf a=> a' ih ?
  xchange fs
  apply hs=> // > /ih
  sapply

lemma structural_imp : structural F ->
  Q ===> Q' -> F Q ==> F Q' := by
  move=> sF h
  xchange sF Q'; unfold mkstruct; xsimp
  apply h

lemma xwhile_inv_basic_lemma (I : Bool -> α -> hProp) R
  (F1 F2 : formula) :
  WellFounded R ->
  structural F1 ->
  structural F2 ->
  (H ==> H' ∗ ∃ʰ b a, I b a) ->
  (∀ b X, I b X ==> F1 (fun bv => I b X ∗ ⌜bv = b⌝)) ->
  (∀ X, I true X ==> F2 (fun _ => ∃ʰ b X', ⌜R X' X⌝ ∗ I b X')) ->
  H ==> wpgen_while F1 F2 (fun _ => H' ∗ ∃ʰ a, I false a) := by
  move=> wf sf1 sf2 hh hf1 hf2
  sorry
  -- apply xwhile_inv_lemma _ _ _ wf=> // > ls fs
  -- xlet; xchange hf1; apply structural_imp sf1=> bv /=
  -- xsimp; xchange mkstruct_erase; xif=> // ->
  -- { xseq; xchange hf2; apply structural_imp sf2=> /= v /= {v}
  --   sby xsimp=> > ?; xchange fs }
  -- xval; xsimp

lemma xwhile_inv_basic_lemmaQ (I : Bool -> α -> hProp) R
  (F1 F2 : formula) :
  WellFounded R ->
  structural F1 ->
  structural F2 ->
  (H ==> H' ∗ ∃ʰ b a, I b a) ->
  (∀ b X, I b X ==> F1 (fun bv => I b X ∗ ⌜bv = b⌝)) ->
  (∀ X, I true X ==> F2 (fun _ => ∃ʰ b X', ⌜R X' X⌝ ∗ I b X')) ->
  ((fun _ => H' ∗ ∃ʰ a, I false a) ===> Q) ->
  H ==> wpgen_while F1 F2 Q := by
  move=> *
  sorry

lemma xwhile_inv_measure_lemma_down (Xbot : Int) (I : Bool -> Int -> hProp)
  (F1 F2 : formula) :
  structural F1 ->
  structural F2 ->
  (H ==> H' ∗ ∃ʰ b a, I b a) ->
  (∀ b X, I b X ==> F1 (fun bv => I b X ∗ ⌜bv = b⌝)) ->
  (∀ X, I true X ==> F2 (fun _ => ∃ʰ b X', ⌜Xbot <= X' /\ X' < X⌝ ∗ I b X')) ->
  ((fun _ => H' ∗ ∃ʰ a, I false a) ===> Q) ->
  H ==> wpgen_while F1 F2 Q := by
  apply xwhile_inv_basic_lemmaQ
  sorry -- wf?

lemma xwhile_inv_measure_lemma_up (Xtop : Int) (I : Bool -> Int -> hProp)
  (F1 F2 : formula) :
  structural F1 ->
  structural F2 ->
  (H ==> H' ∗ ∃ʰ b a, I b a) ->
  (∀ b X, I b X ==> F1 (fun bv => I b X ∗ ⌜bv = b⌝)) ->
  (∀ X, I true X ==> F2 (fun _ => ∃ʰ b X', ⌜X < X' ∧ X' <= Xtop⌝ ∗ I b X')) ->
  ((fun _ => H' ∗ ∃ʰ a, I false a) ===> Q) ->
  H ==> wpgen_while F1 F2 Q := by
  apply xwhile_inv_basic_lemmaQ
  sorry -- wf?

macro "xwhile" I:term:max R:term : tactic => do
  `(tactic| (
    xwp
    xseq_xlet_if_needed_xwp
    xstruct_if_needed
    eapply xwhile_inv_basic_lemmaQ $I $R <;> try simp only [wp_equiv]
    ⟨try assumption,
     try apply wp_structural,
     try apply wp_structural,
     skip,
     skip,
     skip,
     skip,
     skip⟩
    ))

macro "xwhile_up" I:term:max Xtop:term : tactic => do
  `(tactic| (
    xwp
    xseq_xlet_if_needed_xwp
    xstruct_if_needed
    eapply xwhile_inv_measure_lemma_up $Xtop $I <;> try simp only [wp_equiv]
    ⟨try apply wp_structural,
     try apply wp_structural,
     skip,
     skip,
     skip,
     skip,
     skip⟩
    ))

macro "xwhile_down" I:term:max colGt Xbot:term ? : tactic => do
  let Xbot <-
    match Xbot with
    | .some x => pure x
    | .none => `(term| 0)
  `(tactic| (
    xwp
    xseq_xlet_if_needed_xwp
    xstruct_if_needed
    eapply xwhile_inv_measure_lemma_down $Xbot $I <;> try simp only [wp_equiv]
    ⟨try apply wp_structural,
     try apply wp_structural,
     skip,
     skip,
     skip,
     skip,
     skip⟩
    ))
