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

/- ---------- Definition and Structural Rules for [hwp] ---------- -/

/- Definition of [hwp] -/


def hwp (ht : htrm) (Q : hval -> hhProp) : hhProp := (heval s · ht Q)

/- Equivalence b/w [hwp] and [triple] -/

lemma hwp_equiv : H ==> hwp s ht Q = htriple s ht H Q := by rfl

/- Consequence rule for [hwp] -/
lemma hwp_conseq (ht : htrm) (Q Q' : hval -> hhProp) :
  Q ===> Q' -> hwp s ht Q ==> hwp s ht Q' := by
  sby move=> ???/=; apply heval_conseq

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


/- ------------------ Definition of [hwpgen] ------------------ -/

/- Defining [hmkstruct] -/

abbrev hformula := (hval -> hhProp) -> hhProp

local notation "hformula" => @hformula α

def hmkstruct (F : hformula) :=
  fun (Q : hval -> hhProp) => h∃ Q' : hval -> hhProp, F Q' ∗ (Q' -∗ Q)

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
  ypull=> ?
  /- TODO: fix ysimp -/
  sorry

lemma hmkstruct_monotone (F1 F2 : hformula) (Q : hval -> hhProp) :
  (forall Q, F1 Q ==> F2 Q) →
  hmkstruct F1 Q ==> hmkstruct F2 Q :=
by
  move=> Himpl
  srw ?hmkstruct
  ypull=> Q'
  ysimp[Q']
  /- TODO: fix ysimp -/
  sorry


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
  fun Q ↦ h∃ b : Bool, ⌜t = fun _ => trm_val b⌝ ∗ (if b then F₁ Q else F₂ Q)

def hwpgen_if_trm (F₀ F₁ F₂ : hformula) : hformula := hwpgen_let F₀ (fun v => hmkstruct $ hwpgen_if (trm_val ∘ v) F₁ F₂)

def hwpgen_app (s : Set α) (t : htrm) : hformula := fun Q => h∃ H, H ∗ ⌜htriple s t H Q⌝

def hwpgen_for (v₁ v₂ : htrm) (F1 : hval -> hformula) : hformula :=
  hmkstruct fun Q =>
    h∃ n₁ n₂ : Int, ⌜v₁ = fun _ => trm_val n₁⌝ ∗ ⌜v₂ = fun _ => trm_val n₂⌝ ∗
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

------------------------------------------------------------------------------------------------------------------------

structure HFormulaSet where
  F : hformula
  S : Set α

abbrev HFormulaSets (α : Type) := List $ @HFormulaSet α

class inductive HFSSound (t : htrm) : Set α -> outParam (HFormulaSets α) -> Prop where
  | nil : HFSSound t ∅ []
  | cons (s ss : Set α) (F : hformula) : HFSSound t ss hfs -> HWpSound s t ∅ F -> HFSSound t (s ∪ ss) (⟨F, s⟩ :: hfs)

instance : HFSSound t ∅ [] := HFSSound.nil

instance [inst : HFSSound t ss hfs] [inst' : HWpSound s t ∅ F] : HFSSound t (s ∪ ss) (⟨F, s⟩ :: hfs) :=
  HFSSound.cons (t := t) s ss F inst inst'

def seqHstar : List hhProp -> hhProp
  | [] => emp
  | h :: hs => h ∗ seqHstar hs

def HFormulaSets.set_of : HFormulaSets α -> Set α
  | [] => ∅
  | ⟨_, s⟩ :: hfs => s ∪ set_of hfs

def hWp (hfs : HFormulaSets α) (Q : hval -> hhProp) : hhProp :=
  h∃ (Qs : List (hval -> hhProp)) (Q' : hval -> hhProp),
    ⌜List.Forall₂ (∀ hv, hhlocal ·.S $ · hv) hfs Qs⌝ ∗
    ⌜∀ hv, hhlocal hfs.set_of.compl (Q' hv)⌝ ∗
    (seqHstar $ List.zipWith (fun Q ⟨F, _⟩ => F Q) Qs hfs) ∗
    ⌜∀ hv, seqHstar (Qs.map (· hv)) ∗ (Q' hv) ==> Q hv⌝


-- @[simp]
-- def hWp (hfs : HFormulaSets α) (Q : hval -> hhProp) : hhProp :=
--   match hfs with
--   | [] => h∃ hv, Q hv
--   | ⟨F,s⟩ :: hfs => F (fun hv => hWp hfs (fun hv' => Q $ hv ∪_s hv'))

def flocal (s : Set α) (F : hformula) := ∀ (H : hhProp) s' (Q : hval -> hhProp), Disjoint s s' -> hhlocal s' H -> F (Q ∗ H) ==> F Q ∗ H

lemma hWp_focus (i : Nat) (hfs : HFormulaSets α) (_ : i < hfs.length) :
  (hfs.Forall (hstructural ·.F)) ->
  let hf := hfs[i]
  hf.F (fun hv => hWp (hfs.eraseIdx i) (fun hv' => Q $ hv ∪_hf.S hv')) ==> hWp hfs Q := by
  elim: hfs i=> // [F s] hfs ih [] /==
  { move=> sF ssF; sorry }



lemma hWp_sound [HFSSound t s hfs] :
  hWp hfs Q ==> hwp s t Q := by sorry


end HWeakestPrecondition
