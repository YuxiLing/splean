import Lean
-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Common.Util
-- import Lgtm.Unary.WP

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

lemma hwp_conseq' (ht : htrm) (Q Q' : hval -> hhProp) :
  Q ===> (∃ʰ hv, Q' $ · ∪_s hv) -> hwp s ht Q ==> hwp s ht Q' := by
  sby move=> ???/=; apply heval_conseq'

/- Frame rule for [hwp] -/


lemma hwp_frame (ht : htrm) (Q : hval -> hhProp) (H : hhProp) :
  hwp s ht Q ∗ H ==> hwp s ht (Q ∗ H) := by
  move=> ? ![> ?? -> ?];
  apply heval_conseq; apply heval_frame=> //
  ysimp=> //

open Classical

noncomputable def get_sat_val (Q : val → hProp) : val :=
  if ex : ∃ v h, Q v h then choose ex else val_unit

noncomputable def get_sat_heap (Q : hProp) : heap :=
  if ex : ∃ h, Q h then choose ex else ∅

lemma get_sat_heap_of_val (Q : val → hProp) :
  Q v h → ∃ h, Q (get_sat_val Q) h := by
  move=> ?
  have hex:(∃ v h, Q v h) := by exists v, h
  unfold get_sat_val
  srw (dif_pos hex)
  sby apply choose_spec in hex

lemma get_sat_exists (Q : val → hProp) :
  Q v h → Q (get_sat_val Q) (get_sat_heap (Q (get_sat_val Q))) := by
  move=> /[dup] ? /get_sat_heap_of_val
  have hex:(∃ v h, Q v h) := by exists v, h
  unfold get_sat_val
  srw (dif_pos hex)=> hex'
  unfold get_sat_heap
  srw (dif_pos hex')
  sby apply choose_spec in hex'

lemma hSP_sat :
  heval s hh ht hQ -> ∃ hv hh', hSP s hh ht hv hh' := by
  move=> [hQ'] [hevNR _]
  exists fun a ↦ get_sat_val (sP (hh a) (ht a))
  exists (fun a ↦ if a ∈ s then get_sat_heap ((sP (hh a) (ht a))
    (get_sat_val (sP (hh a) (ht a)))) else hh a)
  unfold hSP=> >
  scase_if=> ha
  move: (hevNR a ha)=> {ha hevNR} /sP_sat ![>]
  sby apply get_sat_exists

-- set_option maxHeartbeats 1000000 in
lemma hwp_frame_in (ht : htrm) (Q : hval -> hhProp) (H : hhProp) :
  Disjoint s s' ->
  hwp s ht (Q ∗ ∃ʰ u, hhsingle s' p u) ==> hwp s ht Q ∗ ∃ʰ u, hhsingle s' p u := by
  move=> dj h; unfold hwp=> /=
  scase: [∀ a ∈ s', p a ∈ h a]
  { simp=> a ? pin /[dup] /hSP_sat ![hv hh'] hSPH /[dup] ![? hev _] /hSP_impl /(_ (hSPH)) /=
    scase! => hv' hh₁ hh₂ ? ![v] /= /(_ a); srw if_pos //== => heq
    move=> /(congrArg (a₁ := hh') (· a)) /=; srw heq
    move: hSPH=> /hSP_WellAlloc /(_ hev) /(_ a) /[swap] /(congrArg (a₁ := hh' a) (·.keys))
    move=> -> keq; move: pin; srw -Finmap.mem_keys keq Finmap.mem_keys /==  }
  move=> pin
  let h₁ := fun a => if a ∈ s' then  (h a).erase (p a) else (h a)
  let h₂ :hheap α := (fun a => if a ∈ s' then Finmap.singleton (p a) ((h a).lookup (p a)).get! else ∅)
  shave->: h = h₁ ∪ h₂
  { funext a=> /=; simp [h₁,h₂]; scase_if=> ain //
    srw Finmap.erase_union_singleton
    move: (Finmap.lookup_isSome.mpr (pin _ ain))
    cases eq : (Finmap.lookup (p a) (h a))=> // }
  move=> /heval_frame_in' hev; exists h₁, h₂=> ⟨|⟨|⟨//|⟩⟩⟩ /=
  { apply hev (s' := s')
    { move=> ?; simp [h₂]=> // }
    { sdone }
    { move=> h ![u /= /[swap] a /(_ a)]; simp [h₂]
      scase_if => ? // }
    clear hev
    move=> a; simp [h₁, h₂]; scase_if=> // ?? /== // ??// }
  { clear hev
    exists (fun a => ((h a).lookup (p a)).get!)=> /= a; simp [h₂]
    scase_if=> // }
  clear hev
  move=> a; simp [h₁, h₂]; scase_if=> // ?? /== // ??//


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

lemma hunion_equiv (h₁ h₂ : @hheap α) :
  h₁ ∪ h₂ = fun a ↦ h₁ a ∪ h₂ a := by sdone

lemma hwp_ref (x : α → var) (hv : α → val) (ht : α → trm) (Q : hval → hhProp) :
  (h∀ (p : α → loc), p i ~⟨i in s⟩~> hv i -∗
    hwp s (fun a ↦ subst (x a) (p a) (ht a)) (Q ∗ ∃ʰ (u : α → val), p i ~⟨i in s⟩~> u i)) ==>
  hwp s (fun a ↦ trm_ref (x a) (hv a) (ht a)) Q :=
by
  move=> > /hhforall_inv Hwp ; apply heval_ref=> >
  move: (Hwp hp)=> {Hwp} /hhwand_inv Hwp hmem -- fun i ↦ Finmap.singleton (p i) (hv i)
  specialize Hwp (fun i ↦ if i ∈ s then Finmap.singleton (hp i) (hv i) else ∅)
  have eqn:((fun i ↦ if i ∈ s then Finmap.singleton (hp i) (hv i) else ∅) ∪ h =
    fun i ↦ if i ∈ s then Finmap.insert (hp i) (hv i) (h i) else h i) := by
    { srw hunion_equiv
      apply funext=> > ; sby scase_if }
  srw -eqn
  apply Hwp=> {Hwp} /= >
  { unfold hhsingle bighstar=> /= >
    sby scase_if }
  scase_if=> ?
  { sby unfold Finmap.Disjoint }
  apply Finmap.disjoint_empty

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

def hwpgen_if (s : Set α) (t : htrm) (F₁ F₂ : hformula) : hformula :=
  fun Q ↦ ∃ʰ b : Bool, ⌜∀ a ∈ s, t a = trm_val b⌝ ∗ (if b then F₁ Q else F₂ Q)

def hwpgen_if_trm (s : Set α) (F₀ F₁ F₂ : hformula) : hformula := hwpgen_let F₀ (fun v => hmkstruct $ hwpgen_if s (trm_val ∘ v) F₁ F₂)

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

def wpgen_while (s : Set α) (F1 F2 : hformula) : hformula := hmkstruct fun Q =>
  h∀ R : hformula,
    let F := hwpgen_if_trm s F1 (hwpgen_seq F2 R) (hwpgen_val fun _ => val_unit)
    ⌜hstructural R ∧ F ===> R⌝ -∗ R Q

def hwpgen_ref (s : Set α) (x : α → var) (ht₁ ht₂ : htrm) : hformula :=
  fun Q ↦ ∃ʰ hv : hval, ⌜ht₁ = fun a ↦ trm_val (hv a)⌝ ∗
    h∀ (p : α → loc),
      (p i ~⟨i in s⟩~> hv i) -∗
      protect (hwp s (fun i ↦ subst (x i) (p i) (ht₂ i))
        (fun hv ↦ Q hv ∗ ∃ʰ u : hval, p i ~⟨i in s⟩~> u i))

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

instance  {t₁ t₂ : htrm} :
  HWpSound s (fun a => trm_if (t₀ a) (t₁ a) (t₂ a)) (hwpgen_if s t₀ (hwp s t₁) (hwp s t₂)) := ⟨by
  -- sby
    move=> ?; srw hwpgen_if; ysimp=> b; --scase_if=> ? /== t₀E
    move=> tE; srw [3](hwp_ht_eq (ht₂ := fun a => trm_if b (t₁ a) (t₂ a)))
    { scase_if=> ? /== <;> apply htriple_if=> // }
    move=> * /=; srw tE //⟩

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

instance {x : α → var} {t₁ t₂ : htrm} :
  HWpSound s (fun a ↦ trm_ref (x a) (t₁ a) (t₂ a)) (hwpgen_ref s x t₁ t₂) := ⟨by
  move=> > ; srw hwpgen_ref ; ypull=> > ; apply hwp_ref ⟩

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

lemma wp_cons_last (sht : SHT) (shts : SHTs α) :
  Disjoint sht.s shts.set ->
    wp shts (fun hv => hwp sht.s sht.ht (Q $ · ∪_sht.s hv))
    ==> wp (sht :: shts) Q := by
    move=> /[dup]? /Set.disjoint_left dij;
    srw ?wp /== Set.union_comm hwp_union // hwp_ht_eq
    { apply hwp_conseq=> hv /=
      srw hwp_ht_eq
      { apply hwp_conseq'=> hv' /=; ysimp[hv]
        shave: (hv' ∪_sht.s hv) = hv ∪_shts.set hv' ∪_sht.s hv
        { move=> ! x /==; scase_if <;> scase_if=> // }
        move=> h; srw [1]h // }
      move=> // }
    move=> ? /==; scase_if=> //

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
    move=> ? ![/==???<-]; apply dij1
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

lemma triple_conseq :
  Pre ==> Pre' ->
  Post' ===> Post ->
  triple shts Pre' Post' ->
  triple shts Pre Post := by sorry

lemma wp_frame (Q : hval -> hhProp) (H : hhProp) :
  wp sht Q ∗ H ==> wp sht (Q ∗ H) := by
  apply hwp_frame

lemma triple_extend_univ (Q : hval -> hhProp) :
  shts.set.Nonempty ->
  hhlocal shts.set H ->
  (∀ (hv : hval), hhlocal shts.set (Q hv)) ->
  triple shts (H ∗ [∗ in Set.univ | H']) (Q ∗ [∗ in @Set.univ α| H']) =
  triple shts (H ∗ [∗ in shts.set | H']) (Q ∗ [∗ in shts.set| H'])
   := by
  apply htriple_extend_univ

macro "auto" : tactic => `(tactic|
  try solve
    | omega
    | ((try simp); intros; trivial)
    | solve_by_elim
    | (intros; simp [*]))

syntax "//'" : ssrTriv

macro_rules
  | `(ssrTriv| //') => `(tactic| auto)

theorem Function.invFunOn_app_eq (f : α -> β) [Nonempty α]
  (inj : Set.InjOn f s)
  (h : i ∈ s) : (f.invFunOn s (f i)) = i := by
  apply inj=> //
  srw (Function.invFunOn_apply_eq (f := f)) //

end LGTM

end HWeakestPrecondition
