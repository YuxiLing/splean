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
import Lgtm.Hyper.Subst
-- import Lgtm.Hyper.WPUtil


section HWeakestPrecondition

open Classical trm val prim

variable {α : Type} (s : Set α)

local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

/- ---------- Definition and Structural Rules for [hwp] ---------- -/

/- Definition of [hwp] -/


def hwp (ht : htrm) (Q : hval -> hhProp) : hhProp := (heval s · ht Q)

/- Equivalence b/w [hwp] and [triple] -/

lemma hwp_equiv : H ==> hwp s ht Q = htriple s ht H Q := by rfl

/- Consequence rule for [hwp] -/
lemma hwp_conseq (ht : htrm) (Q Q' : hval -> hhProp) :
  Q ===> Q' -> hwp s ht Q ==> hwp s ht Q' := by
  sby move=> ???/=; apply heval_conseq

lemma hwp_conseq' (ht : htrm) (Q Q' : hval -> hhProp) :
  Q ===> (∃ʰ hv, Q' $ · ∪_s hv) -> hwp s ht Q ==> hwp s ht Q' := by
  sby move=> ???/=; apply heval_conseq'

/- Frame rule for [hwp] -/


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

lemma hwp_swap' (Q : hval -> hhProp) :
  Disjoint s₁ s₂ ->
  hwp s₁ ht (fun hv => hwp s₂ ht (fun hv' => Q (hv ∪_s₁ hv'))) =
  hwp s₂ ht (fun hv => hwp s₁ ht (fun hv' => Q (hv ∪_s₂ hv'))) := by
    move=> ?; sby srw -?hwp_union // Set.union_comm

lemma hwp_swap (Q : hval -> hhProp) :
  Disjoint s₁ s₂ ->
  hwp s₁ ht₁ (fun hv => hwp s₂ ht₂ (fun hv' => Q (hv ∪_s₁ hv'))) =
  hwp s₂ ht₂ (fun hv => hwp s₁ ht₁ (fun hv' => Q (hv ∪_s₂ hv'))) := by
    sorry


@[simp]
lemma fun_insert0: (hv ∪_∅ hv') = hv' := by
  sby funext a; simp [hunion, fun_insert]

lemma hwp0_dep : hwp (∅ : Set α) ht Q = ∃ʰ hv, Q hv := by
  apply hhimpl_antisymm=> h <;> unfold hwp
  { scase! => hQ _ /(_ (fun _ : α => val_unit)) /(_ h) H
    specialize H ?_=> //
    sby scase!: H=> hv' }
  scase! => hv /= ?; exists (fun _ _ _ => True)=> ⟨?//|? h' heq ⟨//|⟩/==⟩
  sby shave<-//: h = h'; funext x; move: (heq x)

lemma hwp0 : hwp (∅ : Set α) ht (fun _ => Q) = Q := by
  sby srw hwp0_dep; apply hhimpl_antisymm=> ?; scase!

lemma hwp_ht_eq :
  (Set.EqOn ht₁ ht₂ s) -> hwp s ht₁ Q = hwp s ht₂ Q := by
  sby move=> ? !?; apply heval_ht_eq

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

lemma hwp_for (n₁ n₂ : α -> Int) (ht : α -> trm) (vr : α -> var) :
  (∀ a ∈ s, n₁ a < n₂ a) ->
  hwp s (fun a => trm_seq (subst (vr a) (n₁ a) (ht a))
                               (trm_for (vr a) (val.val_int $ n₁ a + 1) (n₂ a) (ht a))) Q ==>
  hwp s (fun a => trm_for (vr a) (n₁ a) (n₂ a) (ht a)) Q := by
  sby move=> ??; apply heval_for

lemma hwp_while (cnd ht : α -> trm) :
  (hwp s cnd fun hv => hwp s (fun a => trm_if (hv a) ((ht a).trm_seq (trm_while (cnd a) (ht a))) val.val_unit) Q) ==>
  hwp s (fun a => trm_while (cnd a) (ht a)) Q := by
  sby move=> ?; apply heval_while


lemma hwp_for' (n₁ n₂ : α -> Int) (ht : α -> trm) (vr : α -> var) (Q : hval -> hhProp) :
  (∀ a ∈ s, n₁ a ≥ n₂ a) ->
  Q (fun _ => val.val_unit) ==>
  hwp s (fun a => trm_for (vr a) (n₁ a) (n₂ a) (ht a)) Q := by
  sby move=> ??; apply heval_for'

/- ------------------ Definition of [hwpgen] ------------------ -/

/- Defining [hmkstruct] -/

abbrev hformula := (hval -> hhProp) -> hhProp

local notation "hformula" => @hformula α

def hmkstruct (F : hformula) :=
  fun (Q : hval -> hhProp) => ∃ʰ Q' : hval -> hhProp, F Q' ∗ (Q' -∗ Q)

def hstructural (F : hformula) := forall Q, F Q ==> hmkstruct F Q

def hstructuralPred (F : β -> hformula) := ∀ x, hstructural (F x)

/- [mkstruct F] transforms a formula [F] into one satisfying structural
   rules of Separation Logic. -/

lemma hmkstruct_ramified (Q1 Q2 : hval -> hhProp) F :
  (hmkstruct F Q1) ∗ (Q1 -∗ Q2) ==> (hmkstruct F Q2) :=
by
  srw ?hmkstruct
  ysimp

lemma hmkstruct_erase Q (F : hformula) :
  F Q ==> hmkstruct F Q :=
by
  srw hmkstruct ; ysimp

lemma mkstruct_conseq F (Q1 Q2 : hval -> hhProp) :
  Q1 ===> Q2 →
  hmkstruct F Q1 ==> hmkstruct F Q2 :=
by
  srw ?hmkstruct => h
  ypull=> ?
  unfold hqimpl at *
  ysimp
  sdone

lemma hmkstruct_frame F H (Q : hval -> hhProp) :
  (hmkstruct F Q) ∗ H ==> hmkstruct F (Q ∗ H) :=
by
  srw ?hmkstruct
  ypull=> Q'
  ysimp

lemma hmkstruct_monotone (F1 F2 : hformula) (Q : hval -> hhProp) :
  (forall Q, F1 Q ==> F2 Q) →
  hmkstruct F1 Q ==> hmkstruct F2 Q :=
by
  move=> Himpl
  srw ?hmkstruct
  ypull=> Q'
  ysimp; ychange Himpl; ysimp
  /- TODO: fix ysimp -/


abbrev ctx (α : Type) := AList (fun _ : var ↦ α -> val)

def hwpgen_fail : hformula := fun _ => ⌜False⌝

def hwpgen_val  (v : hval) : hformula := (· v)

def hwpgen_var (E : ctx α) (vr : var) : hformula := fun Q =>
  match AList.lookup vr E with
  | some hv => hwpgen_val hv Q
  | _ => ⌜False⌝

@[simp]
def hwpgen_varE :
  hwpgen_var (E : ctx α) y =
    (match AList.lookup y E with
     | .some hv => hwpgen_val hv
     | _ => fun _ => ⌜False⌝)
    := by
  unfold hwpgen_var=> !? /=
  scase: (AList.lookup y E)=> //
    -- if y ∈ E then hwpgen_val  else hwpgen_fail := by

def hwpgen_fun (s : Set α) (Fof : hval → hformula) : hformula :=
  fun Q ↦ h∀ vf, ⌜forall vx Q', Fof vx Q' ==>
    hwp s (fun a => trm_app (trm_val $ vf a) (trm_val $ vx a)) Q'⌝ -∗ Q vf

def hwpgen_fix (s : Set α) (Fof : hval -> hval → hformula) : hformula :=
  fun Q ↦ h∀ vf, ⌜forall vx Q', Fof vf vx Q' ==>
    hwp s (fun a => trm_app (trm_val $ vf a) (trm_val $ vx a)) Q'⌝ -∗ Q vf


def hwpgen_seq (F₁ F₂ : hformula) : hformula :=
  fun Q ↦ F₁ (fun _ ↦ F₂ Q)


def hwpgen_let (F₁ : hformula) (F₂of : hval -> hformula) : hformula :=
  fun Q ↦ F₁ (fun v ↦ F₂of v Q)

def hwpgen_if (t : htrm) (F₁ F₂ : hformula) : hformula :=
  fun Q ↦ ∃ʰ b : Bool, ⌜t = fun _ => trm_val b⌝ ∗ (if b then F₁ Q else F₂ Q)

def hwpgen_if_trm (F₀ F₁ F₂ : hformula) : hformula := hwpgen_let F₀ (fun v => hmkstruct $ hwpgen_if (trm_val ∘ v) F₁ F₂)

def hwpgen_app (s : Set α) (t : htrm) : hformula := fun Q => ∃ʰ H, H ∗ ⌜htriple s t H Q⌝

def hwpgen_for (v₁ v₂ : htrm) (F1 : hval -> hformula) : hformula :=
  hmkstruct fun Q =>
    ∃ʰ n₁ n₂ : Int, ⌜v₁ = fun _ => trm_val n₁⌝ ∗ ⌜v₂ = fun _ => trm_val n₂⌝ ∗
      h∀ (S : Int -> hformula),
        (let F i :=
          if i < n₂ then
            hwpgen_seq (F1 (fun _ => val_int i)) (S (i + 1))
          else hwpgen_val fun _ => val_unit
        ⌜hstructuralPred S /\ ∀ i, F i ===> S i⌝ -∗ S n₁ Q )

def wpgen_while (F1 F2 : hformula) : hformula := hmkstruct fun Q =>
  h∀ R : hformula,
    let F := hwpgen_if_trm F1 (hwpgen_seq F2 R) (hwpgen_val fun _ => val_unit)
    ⌜hstructural R ∧ F ===> R⌝ -∗ R Q

-- @[simp]
-- abbrev isubst (E : ctx α) (a : α) (t : trm) : trm :=
--   match t with
--   | trm_val v =>
--       v
--   | trm_var x =>
--       match AList.lookup x E with
--       | none   => t
--       | some v => v a
--   | trm_fun x t1 =>
--       trm_fun x (isubst (AList.erase x E) a t1)
--   | trm_fix f x t1 =>
--       trm_fix f x (isubst (AList.erase x (AList.erase f E)) a t1)
--   | trm_if t0 t1 t2 =>
--       trm_if (isubst E a t0) (isubst E a t1) (isubst E a t2)
--   | trm_seq t1 t2 =>
--       trm_seq (isubst E a t1) (isubst E a t2)
--   | trm_let x t1 t2 =>
--       trm_let x (isubst E a t1) (isubst (AList.erase x E) a t2)
--   | trm_app t1 t2 =>
--       trm_app (isubst E a t1) (isubst E a t2)
--   | trm_for x n1 n2 t =>
--       trm_for x (isubst E a n1) (isubst E a n2) (isubst (AList.erase x E) a t)
--   | trm_while c t =>
--       trm_while (isubst E a c) (isubst E a t)

-- @[simp]
-- lemma isubst0 : isubst (∅ : ctx α) = fun _ x => x := by sorry

-- @[simp]
-- lemma subst_isubst (v : hval) (t : htrm) :
--   (fun a => subst x (v a) (isubst (AList.erase x E) a (t a))) =
--   fun a => isubst (AList.insert x v E) a (t a) := by sorry


class HWpSound (s : Set α) (t : htrm) (F : outParam hformula) :=
  impl : ∀ Q, F Q ==> hwp s (fun a => t a) Q

-- @[instance 0]
-- instance : HWpSound (s : Set α) t (∅ : ctx α) (hwp s t) := ⟨by sby srw isubst0⟩

instance : HWpSound s (fun a => trm_val (hv a)) (hwpgen_val hv) := ⟨by sby move=> ? /==; apply htriple_val⟩

@[simp]
lemma hWpSoundTriple {inst: HWpSound s t F} Q : htriple s (fun a => t a) (F Q) Q = true := by
  simp; apply inst.impl

@[simp]
lemma hWpSoundWp {inst: HWpSound s t F} Q : (F Q) ==> hwp s (fun a => t a) Q = true := by
  simp; apply inst.impl

instance {t₁ t₂ : htrm} :
  HWpSound s (fun a => trm_if (t₀ a) (t₁ a) (t₂ a)) (hwpgen_if t₀ (hwp s t₁) (hwp s t₂)) := ⟨by
  -- sby
    move=> ?; srw hwpgen_if; ysimp=> b; scase_if=> ? /== <;> apply htriple_if=> //==⟩

lemma hwp_sound_conseq (F : hformula) :
  F Q ==> hwp s t Q ->
  Q ===> Q' ->
  F Q ==> hwp s t Q' := by
    move=> ??
    sby ychange hwp_conseq

instance {t₁ t₂ : htrm} :
  HWpSound s (fun a => trm_seq (t₁ a) (t₂ a)) (hwpgen_seq (hwp s t₁) (hwp s t₂)) := ⟨by
  move=> Q /==; ychange hwp_seq⟩

instance {x : α -> var} {t₁ t₂ : htrm} :
  HWpSound s (fun a => trm_let (x a) (t₁ a) (t₂ a)) (hwpgen_let (hwp s t₁) (fun hv => hwp s (fun a => subst (x a) (hv a) (t₂ a)))) := ⟨by
  move=> Q /==; ychange hwp_let⟩

instance {t₁ t₂ : htrm} : HWpSound s (fun a => trm_app (t₁ a) (t₂ a)) (hwpgen_app s (fun a => trm_app (t₁ a) (t₂ a))) := ⟨by
  sby move=> Q; srw hwpgen_app; ysimp⟩


lemma hwp_of_hwpgen [inst: HWpSound s t F] :
  H ==> F Q ->
  H ==> hwp s t Q := by
    move=> M; ychange M
    sby srw hWpSoundWp

example :
  ⌜False⌝ ==> hwp {x : Int | x > 0} (fun i => [lang|
    if i > 0 then
       let x := 5 in
       let y := 7 in
       free (x + y);
       y
    else
      y := x + 6;
      6 + 7]) (fun _ => ⌜False⌝) := by
  apply hwp_of_hwpgen=> /==
  ysimp=> //


example :
  ⌜False⌝ ==> hwp {x : Int | x > 0} (fun i => [lang|
       let x := i + 1 in
       let y := 7 in
       x + y]) (fun _ => ⌜False⌝) := by
  apply hwp_of_hwpgen=> /==; simp[subst]
  ysimp=> //


lemma hsubst_hwp (Q : hval -> hhProp) (σ : α -> β) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  (hhlocal s H) ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  H ==> hwp s (ht ∘ σ) Q ->
  hsubst σ s H ==> hwp (ssubst σ s s) ht fun hv => hsubst σ s (Q (hv ∘ σ)) := by
  sby move=> ? Hl ?? ? ![h -> ??]; apply hsubst_heval

lemma hwp_hsubst (Q : hval -> hhProp) (σ : α -> β) :
  hhlocal s H ->
  (∀ hv, hhlocal s (Q hv)) ->
  Set.InjOn σ s ->
  (hsubst σ s H ==> hwp (ssubst σ s s) ht fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  H ==> hwp s (ht ∘ σ) Q := by
  move=> hl ql inj wp h /[dup] /hl {}hl Hh; apply heval_hsubst=> //
  { sby move=> > /ql hl' ? /[dup] /hl -> }
  sby apply wp; exists h=> ⟨//|⟨//|⟩⟩; apply injectiveSet_validSubst


  -- sby move=> ? Hl ?? ? ![h -> ??]; apply hsubst_heval




/- ------------------ LGTM Triple and Weakest Precondition ------------------ -/

namespace LGTM

-- Set and Hyper Term
structure SHT where
  s : Set α
  ht : htrm

instance : Inhabited (@SHT α) := ⟨⟨default, fun _ => default⟩⟩

abbrev SHTs (α : Type) := List $ @SHT α

@[simp]
def SHTs.set : SHTs α -> Set α
  | [] => ∅
  | sht :: shts => sht.s ∪ SHTs.set shts

@[simp]
noncomputable def SHTs.htrm : SHTs α -> htrm
  | [] => fun _ => trm_val val_unit
  | sht :: shts => sht.ht ∪_sht.s SHTs.htrm shts

@[simp]
lemma SHT.set_append (shts₁ shts₂ : SHTs α) :
  SHTs.set (shts₁ ++ shts₂) = SHTs.set shts₁ ∪ SHTs.set shts₂ := by
  sby elim: shts₁=> //= ?? ->; srw ?Set.union_assoc

@[simp]
lemma SHT.htrm_append (shts₁ shts₂ : SHTs α) :
  SHTs.htrm (shts₁ ++ shts₂) = SHTs.htrm shts₁ ∪_shts₁.set SHTs.htrm shts₂ := by
  sby elim: shts₁=> //= ?? ->; srw fun_insert_assoc

def wp (shts : SHTs α) (Q : hval -> hhProp) : hhProp := hwp shts.set shts.htrm Q

lemma wp_cons (sht : SHT) (shts : SHTs α) :
  Disjoint sht.s shts.set ->
    wp (sht :: shts) Q =
    hwp sht.s sht.ht (fun hv => wp shts (Q $ hv ∪_sht.s ·)) := by
    move=> /[dup]? /Set.disjoint_left dij;
    srw ?wp /== hwp_union // hwp_ht_eq
    { sby apply congr=> // !?; apply hwp_ht_eq=> ??; srw fun_insert if_neg }
    sdone

@[simp]
lemma disjoint_shts_set :
  (∀ sht ∈ shts, Disjoint s sht.s) ->
  Disjoint s (SHTs.set shts) = true := by
  sby elim: shts

lemma hwp_Q_eq (Q Q' : hval -> hhProp) :
  (∀ hv, Q hv = Q' hv) -> hwp s ht Q = hwp s ht Q' := by
  sby move=> ?; apply congr=> // !

lemma wp_Q_eq (Q Q' : hval -> hhProp) :
  (∀ hv, Q hv = Q' hv) -> wp sht Q = wp sht Q' := by
  sby move=> ?; apply congr=> // !

lemma fun_insert_comm :
  Disjoint s s' ->
  (f ∪_s g ∪_s' h) = g ∪_s' f ∪_s h := by
    sby move=> /Set.disjoint_left dij !?/==; scase_if

lemma wp_focus (i : Nat) (shts : SHTs α) (_ : i < shts.length) :
  (List.Pairwise (Disjoint ·.s ·.s) shts) ->
  wp shts Q = hwp shts[i].s shts[i].ht fun hv => wp (shts.eraseIdx i) (Q $ hv ∪_shts[i].s ·) := by
  checkpoint (elim: shts Q i=> //= [] s ht shts ih Q [?|i] /==)
  { move=> disj ?; apply wp_cons=> // }
  move=> ? dij1 ?; srw ?wp_cons // hwp_Q_eq; rotate_right
  { move=> ?; rewrite [ih i]
    apply hwp_Q_eq; intros
    apply wp_Q_eq; intros
    rw [<-fun_insert_assoc]=> // }
  srw (hwp_swap (Q := fun hv => wp _ (Q $ hv ∪__ ·)))
  { apply hwp_Q_eq=> ?; srw wp_cons /=;
    { apply hwp_Q_eq=> ?
      apply wp_Q_eq=> ?; srw Set.union_comm fun_insert_assoc }
    srw disjoint_shts_set List.mem_eraseIdx_iff_getElem
    move=> ? ![[]/==???<-]; apply dij1
    apply List.getElem_mem }
  apply dij1; apply List.getElem_mem


lemma wp_squash_tail (sht : SHT) (shts : SHTs α) :
    wp (sht :: shts) Q =
    wp [sht, ⟨shts.set, shts.htrm⟩] Q := by
    sby srw ?wp /==; apply hwp_ht_eq=> ?/== []

lemma wp_unfold_last (shts : SHTs α) :
    shts.getLast? = .some ⟨s ∪ ss, ht ∪_s hts⟩ ->
    wp shts Q =
    wp (shts.dropLast ++ [⟨s, ht⟩, ⟨ss, hts⟩]) Q := by
    move=> le; srw ?wp /==
    srw -[1 2](List.dropLast_append_getLast? (l := shts)) /== -?le //== fun_insert_assoc

lemma wp_unfold_first (shts : SHTs α) :
    Disjoint s s' ->
    wp (⟨s, ht⟩ :: ⟨s', ht'⟩ :: shts) Q =
    wp (⟨s ∪ s', ht ∪_s ht'⟩ :: shts) Q := by
    move=> ?
    srw ?wp /== Set.union_assoc fun_insert_assoc

lemma fun_insert_disjoint :
  Disjoint s s' ->
  ((f ∪_s g) ∪_s' h) = g ∪_s' h := by
  sby move=> /Set.disjoint_left dij !?/==; scase_if=> // /dij


lemma wp_swap :
  Disjoint s s' ->
  wp [⟨s, ht₁⟩, ⟨s', ht'⟩] Q = wp [⟨s', ht'⟩, ⟨s, ht₁⟩] Q := by
  move=> ?
  sby srw ?wp /== Set.union_comm fun_insert_comm


lemma wp_align_step_disj (ht₁ ht₂ ht' : htrm) :
  Disjoint s s' ->
  Disjoint s ss ->
  Disjoint s' ss ->
  wp [⟨s, ht₁⟩, ⟨s', ht'⟩] (fun hv => wp [⟨s, ht₂⟩, ⟨ss, ht'⟩] (Q $ hv ∪_s' ·)) ==>
  wp ([⟨s,fun a => trm_seq (ht₁ a) (ht₂ a)⟩, ⟨s' ∪ ss, ht'⟩]) Q := by
  move=> dij dij' ?
  srw [2]wp_cons //==; ychange hwp_seq
  apply hhimpl_trans_r
  { eapply hwp_conseq=> ? /=; srw -(wp_cons (sht := ⟨s, ht₂⟩))
    { rw [<-(fun_insert_ff (f := ht') (s := s'))]
      srw wp_unfold_last; rotate_right; rfl
      simp; srw (wp_focus 1)=> //== }
    sdone }
  srw wp_cons //= hwp_Q_eq // => ?
  srw wp /= Set.union_empty hwp_ht_eq
  { apply hwp_Q_eq=> ?; apply wp_Q_eq=> ?
    sby srw fun_insert_disjoint }
  sby move=> ?

abbrev triple (shts : SHTs α) (H : hhProp) (Q : hval -> hhProp) : Prop :=
  H ==> wp shts Q

lemma wp_frame (Q : hval -> hhProp) (H : hhProp) :
  wp sht Q ∗ H ==> wp sht (Q ∗ H) := by
  apply hwp_frame

section

local notation t₁ ";; " t₂ => trm_seq t₁ t₂

attribute [simp] Set.disjoint_sdiff_right
attribute [simp] Set.disjoint_sdiff_left

lemma fun_insert_ff_union :
  (f ∪_s₁ f ∪_s₂ g) = f ∪_(s₁ ∪ s₂) g := by
  srw -fun_insert_assoc fun_insert_ff

variable (s' s ss : Set α)
variable (df : α)
variable (dfN : df ∉ s' ∪ s ∪ ss)

lemma hsubst_wp (Q' : _ -> _) (Q : hval -> hhProp) (σ : α -> β) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  (hhlocal s H) ->
  (s = s₁ ∪ s₂) ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  (∀ hv, Q' hv = Q (hv ∘ σ)) ->
  triple
    [⟨s₁, ht₁ ∘ σ⟩, ⟨s₂, ht₂ ∘ σ⟩]
    H
    Q ->
  triple
    [⟨ssubst σ s s₁, ht₁⟩, ⟨ssubst σ s s₂, ht₂⟩]
    (hsubst σ s H)
    fun hv => hsubst σ s (Q' hv) := by sorry


-- @[simp]
private noncomputable def σ' (df : α) : ℕ × α -> α
  | (0, a) => if a ∈ s' ∪ ss then a else df
  | (1, a) => if a ∈ s then a else df
  | _ => df

local notation "σ" => σ' s' s ss df

def labSet (l : ℕ) (s : Set α) : Set (ℕ × α) := {(l, a) | a ∈ s}

notation "⟪" l ", " s "⟫" => labSet l s

@[simp]
lemma labelSet_inE :
  ((l, a) ∈ ⟪l', s⟫) = (l = l' ∧ a ∈ s) := by
  simp [labSet]=> //

@[simp]
lemma labelSet_inE' :
  (⟪l', s⟫ (l, a)) = (l = l' ∧ a ∈ s) := by
  apply labelSet_inE

@[simp]
private lemma foo (s₁ s₂ : Set α):
  (s₁ ∪ s₂) a = (s₁ a ∨ s₂ a) := by rfl



set_option maxHeartbeats 1600000 in
@[simp]
private lemma validSubst_s' :
  Disjoint s' s ->
  Disjoint s' ss ->
  validSubst σ (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0, ss⟫) ⟪0, s'⟫ = true := by
  unfold σ'
  move=> dj₁ dj₂ /== [l x] /== ? l' y ?
  checkpoint (scase: l l'=> //== /[swap] []//== <;> split_ifs=> //)
  { move=> _ /(Set.disjoint_left.mp dj₁) //  }
  move=> /(Set.disjoint_left.mp dj₁) //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma validSubst_sUss :
  Disjoint s' s ->
  Disjoint s' ss ->
  validSubst σ (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0, ss⟫) (⟪1, s⟫ ∪ ⟪0, ss⟫ : Set _) = true := by
  unfold σ'
  move=> dj₁ dj₂ /== [l x] /== ? l' y ?
  checkpoint (scase: l l'=> //== /[swap] []//== <;> split_ifs=> //)
  { move=> [] // /(Set.disjoint_left.mp dj₁) // }
  move=> /(Set.disjoint_left.mp dj₁) //

private lemma ssubst_s' :
  Disjoint s' s ->
  Disjoint s' ss ->
  ssubst σ (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0,ss⟫) ⟪0, s'⟫ = s' := by

  move=> ?? !x; srw fsubst_inE /== => //
  unfold σ'=> /==
  move=> ⟨![a b]|⟩ // ?
  exists 0, x=> //


private lemma ssubst_sUss :
  Disjoint s' s ->
  Disjoint s' ss ->
  ssubst σ (⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0,ss⟫) (⟪1, s⟫ ∪ ⟪0, ss⟫) = s ∪ ss := by
  move=> ?? !x; srw fsubst_inE /== => //
  unfold σ'=> /== ⟨![[]//==]|[]?⟩
  { exists 1, x=> // }
  exists 0, x=> //

private lemma lem0 : ∀ a ∈ s' ∪ s ∪ ss, a ≠ df := by
  move=> ? /[swap]-> //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem1 :
  Disjoint s' s ->
  (∀ a ∈ ⟪1, s⟫ ∪ ⟪0, ss⟫, ∀ a' ∉ ⟪1, s⟫ ∪ ⟪0, ss⟫, σ a ≠ σ a') := by
  unfold σ'
  simp=> /Set.disjoint_left dj [/== b ? [|[]]/==  |]
  { move=> c; split_ifs=> // ?? // }
  { move=> c ?; split_ifs=> // ? // }
  { move=> _; move: (lem0 s' s ss df dfN b)=> // }
  scase=> /== ?? [|[]] /==
  { move=> b ?; split_ifs=> // ? // }
  { move=> b ?; split_ifs; apply lem0=> // }
  move=> _ ⟨//|⟩; apply lem0=> //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem2 :
  Disjoint s' s ->
  ∀ a ∈ ⟪0, s'⟫, ∀ a' ∉ ⟪0, s'⟫, σ a ≠ σ a' := by
  unfold σ'
  move=> /Set.disjoint_left dj [] > //== -> ? [|[]] /==
  { move=> b ?; split_ifs=> // ? // }
  { move=> c; split_ifs=> // ? // }
  move=> _ ⟨//|⟩; apply lem0=> //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem3 :
  Disjoint s' s ->
  Disjoint s' ss ->
  ∀ a ∈ ⟪0, s'⟫, ∀ b ∈ ⟪1, s⟫ ∪ ⟪0, ss⟫, σ a ≠ σ b := by
  unfold σ'
  simp=> /Set.disjoint_left ? /Set.disjoint_left ? [] /== ?? [|[]] /==
  { move=> b ?; split_ifs=> // ? // }
  move=> b ?; split_ifs=> // ? //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem4 :
  ∀ a ∈ ⟪0, s'⟫ ∪ (⟪1, s⟫ ∪ ⟪0, ss⟫), ∀ a' ∉ ⟪0, s'⟫ ∪ (⟪1, s⟫ ∪ ⟪0, ss⟫), σ a ≠ σ a' := by
  unfold σ'
  move: dfN
  simp=> ??? [|[]] /== ? H [|[]] /== *
  { scase_if=> /== <;> scase_if=> //==
    move=> ?? [] ?? // }
  { scase_if=> /== <;> scase_if=> //==
    move=> ? [] ?? // }
  { scase: H=> // ? ⟨//|?//⟩ }
  { scase_if=> /== <;> scase_if=> //==
    move=> ???? // }
  { scase_if=> /== <;> scase_if=> //==
    move=> ??? // }
  move=> ⟨//|?//⟩



macro "auto" : tactic => `(tactic|
  try solve
    | omega
    | ((try simp); intros; trivial)
    | solve_by_elim
    | (intros; simp [*]))

syntax "//'" : ssrTriv

macro_rules
  | `(ssrTriv| //') => `(tactic| auto)

@[simp]
lemma disjoint_labSet :
  Disjoint ⟪l, s⟫ ⟪l', s'⟫ = (l ≠ l' ∨ Disjoint s s') := by
  sorry


lemma triple_Q_eq
  (Q Q' : hval -> hhProp) :
  (∀ hv, Q hv = Q' hv) -> triple shts H Q = triple shts H Q' := by
  sorry

-- @[simp]
private noncomputable def ι' (df : α) : α -> ℕ × α := λ a =>
  if a ∈ s' then (0, a) else if a ∈ s then (1, a) else (2, df)

local notation "σ" => σ s' s df

lemma wp2_ht_eq :
  Set.EqOn ht₁ ht₁' s₁ ->
  Set.EqOn ht₂ ht₂' s₂ ->
  wp [⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩] Q =
  wp [⟨s₁, ht₁'⟩, ⟨s₂, ht₂'⟩] Q := by sorry

local notation "ι" => ι' s' s df

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem5 :
  Disjoint s' s ->
  ∀ a ∈ s' ∪ s, ∀ a' ∉ s' ∪ s, ι a ≠  ι a' := by
  unfold ι'
  simp=> /Set.disjoint_left dj ? [] *
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem6 :
  Disjoint s' s ->
  ∀ a ∈ s', ∀ a' ∈ s, ι a ≠  ι a' := by
  unfold ι'
  simp=> /Set.disjoint_left dj ? *
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem9 :
  ∀ a ∈ s', ∀ a' ∉ s', ι a ≠  ι a' := by
  unfold ι'
  simp=> ? *
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem12 :
  Disjoint s' s ->
  ∀ a ∈ s, ∀ a' ∉ s, ι a ≠  ι a' := by
  unfold ι'
  simp=> /Set.disjoint_left dj ? *
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem10 :
  validSubst ι (s' ∪ s) s' := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem11 :
  validSubst ι (s' ∪ s) s := by
  unfold ι'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

-- Set.EqOn ht₁ ((ht₁ ∘ σ) ∘ ι) s'

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem7 :
  Disjoint s' s ->
  Set.EqOn f ((f ∘ σ) ∘ ι) s := by
  unfold ι' σ'
  move=> dj₁ ? /== ?; srw if_neg /== ?if_pos //' => ?
  apply (Set.disjoint_left.mp dj₁)=> //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem8 :
  Set.EqOn f ((f ∘ σ) ∘ ι) s' := by
  unfold ι' σ'
  move=> ? /== ?; srw if_pos /== //'

set_option maxHeartbeats 1600000 in
private lemma lem13 :
  ssubst ι (s' ∪ s) s' = ⟪0, s'⟫ := by
  unfold ι'
  move=> ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem10=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  exists x=> //

set_option maxHeartbeats 1600000 in
private lemma lem14 :
  Disjoint s' s ->
  ssubst ι (s' ∪ s) s = ⟪1, s⟫ := by
  unfold ι'
  move=> /Set.disjoint_left dj ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem11=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  { split_ifs=> // }
  exists x; split_ifs=> //

private noncomputable def κ' (df : α) : α -> ℕ × α := λ a =>
  if a ∈ s' then (0, a) else if a ∈ ss then (0, a) else (2, df)

local notation "κ " => κ' s' ss df

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem5' :
  Disjoint s' ss ->
  ∀ a ∈ s' ∪ ss, ∀ a' ∉ s' ∪ ss, κ a ≠ κ a' := by
  unfold κ'
  simp=> /Set.disjoint_left dj ? [] *
  all_goals split_ifs=> //
  -- simp: dfN=> ???
  -- move=> ? /== [] ?
  -- { srw if_pos //== => ???
  --   scase_if=> [[]|] ? <;> srw if_neg //
  --   all_goals srw if_neg //== => ? // }
  -- move=> ??; scase_if=> //
  -- scase_if=> //
  -- scase_if=> //
  -- scase_if=> // * ? //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem6' :
  Disjoint s' ss ->
  ∀ a ∈ s', ∀ a' ∈ ss, κ a ≠ κ a' := by
  unfold κ'
  simp=> /Set.disjoint_left dj ? *
  all_goals split_ifs=> // ? //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem9' :
  ∀ a ∈ s', ∀ a' ∉ s', κ a ≠  κ a' := by
  unfold κ'
  simp=> ? *
  all_goals split_ifs=> // ? //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem12' :
  Disjoint s' ss ->
  ∀ a ∈ ss, ∀ a' ∉ ss, κ a ≠ κ a' := by
  unfold κ'
  simp=> /Set.disjoint_left dj ? *
  all_goals split_ifs=> // ? //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem10' :
  validSubst κ (s' ∪ ss) s' := by
  unfold κ'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

set_option maxHeartbeats 1600000 in
-- @[simp]
private lemma lem11' :
  validSubst κ (s' ∪ s) s := by
  unfold κ'
  move=> ?/== [] ? ? [] ?
  all_goals split_ifs=> //

-- Set.EqOn ht₁ ((ht₁ ∘ σ) ∘ ι) s'

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem7' :
  Disjoint s' ss ->
  Set.EqOn f ((f ∘ σ) ∘ κ) ss := by
  unfold κ' σ'
  move=> dj₁ ? /== ?; srw if_neg /== ?if_pos //' => ?
  apply (Set.disjoint_left.mp dj₁)=> //

set_option maxHeartbeats 1600000 in
@[simp]
private lemma lem8' :
  Set.EqOn f ((f ∘ σ) ∘ κ) s' := by
  unfold κ' σ'
  move=> ? /== ?; srw if_pos /== //'

set_option maxHeartbeats 1600000 in
private lemma lem13' :
  ssubst κ (s' ∪ ss) s' = ⟪0, s'⟫ := by
  unfold κ'
  move=> ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem10'=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  exists x=> //

set_option maxHeartbeats 1600000 in
private lemma lem14' :
  Disjoint s' ss ->
  ssubst κ (s' ∪ ss) ss = ⟪0, ss⟫ := by
  unfold κ'
  move=> /Set.disjoint_left dj ! [l x]
  srw fsubst_inE /==; rotate_left
  { apply lem11'=> // }
  move=> ⟨/== ? [] ?? //|/== ->?⟩
  -- { split_ifs=> // }
  exists x; split_ifs=> //

set_option maxHeartbeats 1600000 in
lemma wp_align_step_non_disj_aux
  (ht₁ ht₂ ht : htrm)
  (Q  : α -> hval -> hval -> hProp)
  (Q' : α -> hval -> hProp)
  (H : α -> hProp) (R R' : α -> hProp)  :
  (∀ hv₁ hv₂ hv₁' hv₂', ∀ a ∈ s',
    Set.EqOn hv₁ hv₁' s ->
    Set.EqOn hv₂ hv₂' ss ->
    Q a hv₁ hv₂ = Q a hv₁' hv₂') ->
  (∀ hv₁ hv₁', ∀ a ∈ s',
    Set.EqOn hv₁ hv₁' s ->
    Q' a hv₁ = Q' a hv₁') ->
  Disjoint s' s ->
  Disjoint s' ss ->
  triple
    [⟨s', ht₁⟩, ⟨s, ht⟩]
    ([∗ i in s'| H i] ∗ [∗ i in s| R  i])
    (fun hv => [∗ i in s' | Q' i hv] ∗ [∗ i in s| R' i]) ->
  (∀ hv : hval, triple
          [⟨s', ht₂⟩, ⟨ss, ht⟩]
          ([∗ i in s' | Q' i hv] ∗ [∗ i in ss| R  i])
          (fun hv' => [∗ i in s' | Q i hv hv'] ∗ [∗ i in ss| R' i])) ->
  triple
     [⟨s',fun a => ht₁ a;; ht₂ a⟩, ⟨s ∪ ss, ht⟩]
     ([∗ i in s'| H i] ∗ [∗ i in s ∪ ss| R  i])
     (fun hv => [∗ i in s' | Q i hv hv] ∗ [∗ i in s ∪ ss| R' i]) := by
  move=> eqQ eqQ' dj₁ dj₂ tr₁ tr₂
  srw -(ssubst_s' (s' := s') (s := s) (ss := ss) (df := df)) //'
  srw -(ssubst_sUss (s' := s') (s := s) (ss := ss) (df := df)) //'
  shave ?: ∀ a ∈ ⟪0, s'⟫, ∀ a' ∉ ⟪0, s'⟫, σ a ≠ σ a'
  { apply lem2=> //' }
  shave ?: ∀ a ∈ ⟪1, s⟫ ∪ ⟪0, ss⟫, ∀ a' ∉ ⟪1, s⟫ ∪ ⟪0, ss⟫, σ a ≠ σ a'
  { apply lem1=> //' }
  shave ?: ⟪1, s⟫ ∪ ⟪0, ss⟫ ⊆ ⟪0, s'⟫ ∪ ⟪1, s⟫ ∪ ⟪0, ss⟫
  { move=> x /== [] //' }
  shave ?: ∀ a ∈ ⟪0, s'⟫, ∀ b ∈ ⟪1, s⟫ ∪ ⟪0, ss⟫, σ a ≠ σ b
  { apply lem3=> //' }
  srw -?hsubst_bighstar //'
  srw (hsubst_hhstar _ ⟪0, s'⟫ (⟪1, s⟫ ∪ ⟪0, ss⟫)) ?Set.union_assoc //'
  srw triple_Q_eq; rotate_right
  { move=> ?;
    rewrite [<-Set.union_assoc, <-hsubst_bighstar]
    { srw (hsubst_hhstar _ ⟪0, s'⟫ (⟪1, s⟫ ∪ ⟪0, ss⟫)) ?Set.union_assoc //' }
    all_goals auto }
  srw ?Set.union_assoc
  apply
     hsubst_wp
       (α := _)
       (s := _)
       (Q' := fun hv => [∗i in _| Q _ hv hv] ∗ _)
       (Q := fun hv => [∗i in ⟪0, s'⟫| Q (σ i) (hv ∘ (1,·)) (hv ∘ (0,·))] ∗
                       [∗i in ⟪1, s⟫ ∪ ⟪0, ss⟫| R' (σ i)])=> //'
  -- { apply lem4=> //' }
  { move=> > hvEq; congr
    apply bighstar_eq=> [] [] /== a ?
    unfold σ'=> /==
    srw if_pos //'; apply eqQ=> //' a' /== ? <;> apply hvEq=> //' }
  { move=> hv; congr; apply bighstar_eq=> [] [] /== a ?
    unfold σ'=> /==
    srw if_pos //'; apply eqQ=> //' a' /== ? <;> srw if_pos //' }
  srw triple; apply hhimpl_trans_r; apply wp_align_step_disj=> //'
  clear *- tr₁ tr₂ dj₁ dj₂ eqQ eqQ' dfN
  srw triple (wp2_ht_eq (ht₁' := (ht₁ ∘ σ) ∘ ι) (ht₂' := (ht ∘ σ) ∘ ι)) at tr₁
  rotate_left
  { move=> ? /== ?; unfold ι' σ'=> /==; srw if_pos /== //' }
  { move=> ? /== ?; unfold ι' σ'; srw if_neg /== ?if_pos //' => ?
    apply (Set.disjoint_left.mp dj₁)=> // }
  apply hsubst_wp (s := s' ∪ s) (Q' := _) at tr₁=> //'; rotate_left
  { apply lem5=> //' }
  { move=> > seq; congr; apply bighstar_eq=> ??
    apply eqQ'=> //' ??; apply seq=> //' }
  srw -(hsubst_hhstar (s₁ := s') (s₂ := s)) //' at tr₁; rotate_left
  { apply lem6=> //' }
  shave ?: ∀ β, ∀ f : α -> β, ∀ a ∈ s, f a = f (σ (ι a))
  { move=> ??; apply lem7=> //' }
  shave ?: ∀ β, ∀ f : α -> β, ∀ a ∈ s', f a = f (σ (ι a))
  { move=> ??; apply lem8=> //' }
  shave ?:  ∀ a ∈ s', ∀ a' ∉ s', ι a ≠ ι a'
  { apply lem9=> //' }
  shave ?: validSubst ι (s' ∪ s) s
  { apply lem11=> //' }
  shave ?: validSubst ι (s' ∪ s) s'
  { apply lem10=> //' }
  shave ?:  ∀ a ∈ s, ∀ a' ∉ s, ι a ≠ ι a'
  { apply lem12=> //' }
  srw (bighstar_eq (H' := fun i => H (σ (ι i)))) //' at tr₁
  srw [2](bighstar_eq (H' := fun i => R (σ (ι i)))) //' at tr₁
  srw (hsubst_bighstar ι (H := fun i => H (σ i))) //' at tr₁
  srw (hsubst_bighstar ι (H := fun i => R (σ i))) //' at tr₁
  srw lem13 //' lem14 //' at tr₁
  srw triple_Q_eq at tr₁; rotate_right
  { move=> hv
    rewrite [bighstar_eq (H' := fun i => Q' (σ (ι i)) (hv ∘ ι))]
    rewrite (config := {occs := .pos [2]}) [bighstar_eq (H' := fun i => R' (σ (ι i)))]
    rewrite [<-hsubst_hhstar (s₁ := s') (s₂ := s)]
    rewrite [hsubst_bighstar ι (H := fun i => Q' (σ i) (hv ∘ ι))]
    rewrite [hsubst_bighstar ι (H := fun i => R' (σ i))]
    rewrite [lem13]; rewrite [lem14]
    rfl
    all_goals auto
    apply lem6=> // }
  clear *- tr₁ tr₂ dj₁ dj₂ eqQ eqQ' dfN
  srw triple at tr₁
  srw -bighstar_hhstar_disj //'
  ychange tr₁
  shave->: OfNat.ofNat 1 = 1; rfl
  shave->: OfNat.ofNat 0 = 0; rfl
  apply hhimpl_trans; apply wp_frame
  apply hwp_conseq=> hv /=
  srw hhstar_assoc [2]hhstar_comm -hhstar_assoc
  srw [2]Set.union_comm -bighstar_hhstar_disj //'
  srw wp_Q_eq; rotate_left 2
  { move=> ?; srw -hhstar_assoc }
  apply hhimpl_trans_r; apply wp_frame; ysimp
  shave->: OfNat.ofNat 1 = 1; rfl
  shave->: OfNat.ofNat 0 = 0; rfl
  srw -(lem14' s' ss df) //' -(lem13' s' ss df)
  shave ?: ∀ β : Type, ∀ f : α -> β, ∀ a ∈ ss, f a = f (σ (κ a))
  { move=> ??; apply lem7'=> //' }
  shave ?: ∀ β : Type, ∀ f : α -> β, ∀ a ∈ s', f a = f (σ (κ a))
  { move=> ??; apply lem8'=> //' }
  shave ?:  ∀ a ∈ s', ∀ a' ∉ s', κ a ≠ κ a'
  { apply lem9'=> //' }
  shave ?: validSubst κ (s' ∪ ss) ss
  { apply lem11'=> //' }
  shave ?: validSubst κ (s' ∪ ss) s'
  { apply lem10'=> //' }
  shave ?:  ∀ a ∈ ss, ∀ a' ∉ ss, κ a ≠ κ a'
  { apply lem12'=> //' }
  srw -?hsubst_bighstar //' (hsubst_hhstar (s₁ := s') (s₂ := ss)) //'; rotate_left
  { apply lem6'=> //' }
  srw wp_Q_eq; rotate_left 2
  { move=> hv₁'
    rewrite [<-hsubst_bighstar]
    { srw (hsubst_hhstar (s₁ := s') (s₂ := ss)) //'
      apply lem6'=> //'  }
    all_goals auto }
  shave σκ: ∀ a ∈ s' ∪ ss, σ (κ a) = a
  { move=> ? /== []? <;> apply Eq.symm;
    { apply (lem8' (f := id))=> //' }
    apply (lem7' (f := id))=> //' }
  eapply (hsubst_wp (Q := fun hv' => [∗i in s'| Q i (hv ∘ ι) hv'] ∗ [∗i in ss| R' i]))=> //'
  { apply lem5'=> //' }
  { move=> > hvEq; congr
    apply bighstar_eq=> ??; unfold ι'; apply eqQ=> //' ??
    apply hvEq=> //' }
  { move=> hv'; congr <;> apply bighstar_eq=> ??
    { srw σκ //'; unfold κ'; apply eqQ=> //' ? xin //'
      unfold ι'=> /==;
      { srw if_pos //' if_neg //'
        apply (Set.disjoint_left.mp _ xin)=> //' }
      srw if_neg //' ?if_pos //'
      apply (Set.disjoint_left.mp _ xin)=> //' }
    srw σκ //' }
  srw triple wp2_ht_eq;
  { apply hhimpl_trans_r; apply tr₂
    srw bighstar_eq
    { srw [2]bighstar_eq; apply hhimpl_refl
      move=> *; srw σκ //' }
    move=> *; srw σκ //' }
  { move=> ?? /==; srw σκ //' }
  move=> ?? /==; srw σκ //'

end

section wp_align_step_non_disj

lemma wp_hsubst_some [Inhabited α] (Q : hval -> hhProp) :
  s = s₁ ∪ s₂ ->
  hhlocal s H ->
  (∀ hv, hhlocal s (Q hv)) ->
  triple
    [⟨ssubst some s s₁, ht₁ ∘ Option.get!⟩, ⟨ssubst some s s₂, ht₂ ∘ Option.get!⟩]
    (hsubst some s H)
    (fun hv => hsubst some s (Q (hv ∘ some))) ->
  triple
    [⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩]
    H
    Q := by sorry

attribute [simp] Option.any

@[simp]
private lemma ssubst_some_inE [Inhabited α] (s s' : Set α) (x : Option α) :
  x ∈ ssubst some s s' ↔ (∃ y ∈ x, (y ∈ s ∩ s')) := by
  srw fsubst_inE => [⟨|⟩|?//] /==
  { move=> ??? <- /== // }
  sby scase: x

private lemma lem (s₁ s₂) [Inhabited α] (H₁ H₂ : α -> hProp) :
  Disjoint s₁ s₂ ->
  s = s₁ ∪ s₂ ->
  hsubst some s (bighstar s₁ H₁ ∗ bighstar s₂ H₂) =
  [∗ i in ssubst some s s₁| H₁ i.get!] ∗
  [∗ i in ssubst some s s₂| H₂ i.get!] := by
  move=> /[dup] /Set.disjoint_left ?? ->
  srw -(hsubst_hhstar (s₁ := s₁) (s₂ := s₂)) //'; rotate_left
  { move=> ?? ?? [] // }
  srw (bighstar_eq (H' := (H₁ ∘ Option.get!) ∘ some)) //
  srw [2](bighstar_eq (H' := (H₂ ∘ Option.get!) ∘ some)) //
  generalize heq: (H₁ ∘ Option.get!) = H'
  generalize req: (H₂ ∘ Option.get!) = R'=> /=
  srw ?hsubst_bighstar //'; rotate_left
  { move=> * [] // }
  { move=> // }
  { move=> * [] // }
  { move=> // }
  subst_vars=> /== //

private lemma ssubst_some_union [Inhabited α] (s s₁ s₂ : Set α) :
  ssubst some s (s₁ ∪ s₂) =
  ssubst some s s₁ ∪ ssubst some s s₂ := by
  move=> ! [] /== v ⟨|⟩ // [] //

private lemma ssubst_some_disjoint [Inhabited α] :
  Disjoint s₁ s₂ ->
  Disjoint (ssubst some s s₁) (ssubst some s s₂) := by
  move=> /Set.disjoint_left dj
  srw Set.disjoint_left=> /== ?? -> //

private lemma lem_s'1 [Inhabited α] :
  ssubst some (s' ∪ (s ∪ ss)) s' =
  ssubst some (s' ∪ s) s' := by
  move=> !x /== ⟨|⟩ /==//

private lemma lem_s'2 [Inhabited α] :
  ssubst some (s' ∪ (s ∪ ss)) s' =
  ssubst some (s' ∪ ss) s' := by
  move=> !x /== ⟨|⟩ /==//

private lemma lem_s [Inhabited α] :
  ssubst some (s' ∪ (s ∪ ss)) s =
  ssubst some (s' ∪ s) s := by
  move=> !x /== ⟨|⟩ /==//

private lemma lem_ss [Inhabited α] :
  ssubst some (s' ∪ (s ∪ ss)) ss =
  ssubst some (s' ∪ ss) ss := by
  move=> !x /== ⟨|⟩ /==//


attribute [-simp] Option.any

set_option maxHeartbeats 1600000 in
lemma wp_align_step [Inhabited α]
  (ht₁ ht₂ ht : htrm)
  (Q  : α -> hval -> hval -> hProp)
  (Q' : α -> hval -> hProp)
  (H : α -> hProp) (R R' : α -> hProp)  :
  (∀ hv₁ hv₂ hv₁' hv₂', ∀ a ∈ s',
    Set.EqOn hv₁ hv₁' s ->
    Set.EqOn hv₂ hv₂' ss ->
    Q a hv₁ hv₂ = Q a hv₁' hv₂') ->
  (∀ hv₁ hv₁', ∀ a ∈ s',
    Set.EqOn hv₁ hv₁' s ->
    Q' a hv₁ = Q' a hv₁') ->
  Disjoint s' s ->
  Disjoint s' ss ->
  triple
    [⟨s', ht₁⟩, ⟨s, ht⟩]
    ([∗ i in s'| H i] ∗ [∗ i in s| R  i])
    (fun hv => [∗ i in s' | Q' i hv] ∗ [∗ i in s| R' i]) ->
  (∀ hv : hval, triple
          [⟨s', ht₂⟩, ⟨ss, ht⟩]
          ([∗ i in s' | Q' i hv] ∗ [∗ i in ss| R  i])
          (fun hv' => [∗ i in s' | Q i hv hv'] ∗ [∗ i in ss| R' i])) ->
  triple
     [⟨s',fun a => trm_seq (ht₁ a) (ht₂ a)⟩, ⟨s ∪ ss, ht⟩]
     ([∗ i in s'| H i] ∗ [∗ i in s ∪ ss| R  i])
     (fun hv => [∗ i in s' | Q i hv hv] ∗ [∗ i in s ∪ ss| R' i]) := by
  move=> eqQ eqQ' *
  eapply wp_hsubst_some=> //'
  srw lem //' triple_Q_eq;  rotate_left 2
  { move=> hv; apply lem=> // }
  srw Function.comp /= ssubst_some_union
  eapply (wp_align_step_non_disj_aux
    (Q := fun i hv hv' => Q i.get! (hv ∘ some) (hv' ∘ some))
    (Q' := fun i hv => Q' i.get! (hv ∘ some))
    (df := none))=> //==
  { move=> > -> ?? eq₁ eq₂
    apply eqQ=> //' ? /==?; apply eq₁=> //; apply eq₂=> // }
  { move=> > -> ?? eq₁
    apply eqQ'=> //' ? /==?; apply eq₁=> // }
  { apply ssubst_some_disjoint=> // }
  { apply ssubst_some_disjoint=> // }
  { srw lem_s'1 lem_s -(lem _ s' s) // triple_Q_eq; rotate_left 2
    { move=> hv; srw -(lem _ s' s (H₁ := fun i => Q' i (hv ∘ some))) // }
    apply hsubst_wp=> //
    { move=> ?? ?? [] // }
    { move=> > eq; congr; apply bighstar_eq=> ??; apply eqQ'=> // }
    sdone }
  move=> hv
  srw lem_s'2 lem_ss -(lem _ s' ss (H₁ := fun i => Q' i (hv ∘ some))) //
  srw triple_Q_eq; rotate_left 2
  { move=> hv'; srw -(lem _ s' ss (H₁ := fun i => Q i (hv ∘ some) (hv' ∘ some))) // }
  apply hsubst_wp=> //
  { move=> ?? ?? [] // }
  { move=> > eq₁; congr; apply bighstar_eq=> ??; apply eqQ=> // }
  sdone

end wp_align_step_non_disj

end LGTM

end HWeakestPrecondition
