-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog

import Lgtm.Hyper.HProp

section HSepLog

open Classical

variable {α : Type}

def htrm (α : Type) := α -> trm
def hval (α : Type) := α -> val

local notation "hheap"  => @hheap α
local notation "hhProp" => @hhProp α
local notation "htrm"   => @htrm α /- Program Product -/
local notation "hval"   => @hval α

open trm val

/- ================= Hyper Semantics for Program Products ================= -/

section heval

/- -------------- Hyper-Evaluation Definition -------------- -/

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


def heval (s : Set α) (hh : hheap) (ht : htrm) (hQ : hval -> hhProp) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> h∃ hv', hQ (hv ∪_s hv')
    /-                    hQ'                      ==>         hQ -/

/- -------------- Hyper-Evaluation Properties -------------- -/

/- **Frame** Rule -/
lemma heval_nonrel_conseq (s : Set α) :
  heval_nonrel s hh t Q1 →
  (∀ a ∈ s, qimpl (Q1 a) $ Q2 a) →
  heval_nonrel s hh t Q2 := by
  sby move=> hev qimp a /[dup] ain/hev/eval_conseq /(_ (qimp a ain))

lemma heval_conseq :
  heval s hh t Q1 →
  Q1 ===> Q2 →
  heval s hh t Q2 := by
  scase! => ?? himp qimp ⟨//|⟩
  sby constructor=> // hv ? /himp; apply hhimpl_hhexists

lemma heval_nonrel_frame :
  heval_nonrel s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval_nonrel s (hh1 ∪ hh2) t (fun a => Q a ∗ (fun hh ↦ hh = hh2 a)) := by
  sby move=> hev ?? /hev /eval_frame

lemma heval_frame :
  heval s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval s (hh1 ∪ hh2) t (Q ∗ (· = hh2)) := by
  scase! => hQ ? himp ?
  exists fun a => hQ a ∗ (· = hh2 a)=> ⟨|hv⟩
  { sby apply heval_nonrel_frame }
  srw qstarE hqstarE -bighstarDef_hhstar // bighstarDef_eq
  srw -hhstar_hhexists_l
  sby apply hhimpl_hhstar_trans_l


/- **Prod** Rule -/

/-   ∀ i ∈ s, { Hᵢ } [P i] { Qᵢ }
 ----------------------------------------
 { ∗_(i ∈ s) Hᵢ } [s : P] { ∗_(i ∈ s) Qᵢ }
 -/
lemma heval_prod' (hQ : α -> val -> hProp) :
  (∀ a ∈ s, eval (hh a) (ht a) (hQ a)) ->
  heval s hh ht fun hv => bighstarDef s (fun a => hQ a (hv a)) hh := by
  move=> hev; exists hQ=> ⟨|hv ⟩ //
  sby apply (hhimpl_hhexists_r hv); srw fun_insert_ff

lemma heval_prod (hQ : α -> val -> hProp) :
  (∀ a ∈ s, eval (hh a) (ht a) (hQ a)) ->
  (∀ a ∉ s, hh a = hh₀ a) ->
  heval s hh ht fun hv => bighstarDef s (fun a => hQ a (hv a)) hh₀ := by
  move=> *; apply heval_conseq
  { apply heval_prod'=> // }
  sby move=> ? /=; srw bighstarDef_def_eq


/- Stronges Hyper Post Condition -/

abbrev isHStrongestPostNonrel (s : Set α) h t (sP : α -> _) :=
  ∀ Q, heval_nonrel s h t Q -> ∀ a ∈ s, qimpl (sP a) (Q a)

abbrev hStrongestPostNonrel (hh : hheap) (ht : htrm) :=
  fun a => sP (hh a) (ht a)


lemma hstrongest_postP :
  isHStrongestPostNonrel s hh ht (hStrongestPostNonrel hh ht) := by
  move=> Q ? a ?? /=; apply himpl_hforall_l _ (Q a)
  sby srw hwand_hpure_l


lemma hstrongest_post_provable :
  heval_nonrel s hh ht hQ -> heval_nonrel s hh ht (hStrongestPostNonrel hh ht) := by
  move=> hev a /hev; unfold hStrongestPostNonrel
  apply sP_post

lemma heval_strongest :
  heval s hh ht hQ ->
  ∃ (hQ' : α -> val -> hProp),
    isHStrongestPostNonrel s hh ht hQ' ∧
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> h∃ hv', hQ (hv ∪_s hv') := by
  scase! => hQ ? himp; exists hStrongestPostNonrel hh ht
  repeat' constructor
  { sby apply hstrongest_postP }
  { sby apply hstrongest_post_provable }
  move=> hv; apply hhimpl_trans_r; apply himp
  apply bighstarDef_himpl=> ??
  sby apply hstrongest_postP


/- **Unfocus** Rule -/

lemma heval_nonrel_split :
  heval_nonrel s₁ hh ht hQ ->
  heval_nonrel s₂ hh ht hQ ->
  heval_nonrel (s₁ ∪ s₂) hh ht hQ := by
  sby move=> hev₁ hev₂ ? /== [/hev₁|/hev₂]

lemma heval_nonrel_sat :
  heval_nonrel s h t Q ->
    ∃ (hh : hheap) (hv : hval), ∀ a ∈ s, Q a (hv a) (hh a) := by
    move=> ev
    shave: ∃ (hhv : α -> heap × val), ∀ a ∈ s, Q a (hhv a).2 (hhv a).1
    { srw -(@skolem _ (fun _ => heap × val) (fun a b => a ∈ s -> Q a b.2 b.1))
      move=> x; scase: [x ∈ s]
      { move=> ?; constructor=> // }
      move=> /ev /eval_sat ![]h v ?
      sby exists (v,h)=> ? }
    scase=> hhv H; exists (fun a => (hhv a).1), (fun a => (hhv a).2)


lemma heval_nonrel_sat' :
  heval_nonrel s h t Q ->
    ∃ (hh : hheap) (hv : hval), (∀ a ∈ s, Q a (hv a) (hh a)) ∧ (∀ a ∉ s, hh a = h a) := by
    move=> /heval_nonrel_sat ![hh hv H]
    sby exists (hh ∪_s h), hv



lemma heval_unfocus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval (s₁ ∪ s₂) hh ht hQ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) := by
  move=> /Set.disjoint_left dj ![hQ₁ hev] /= himp
  exists (fun a => if a ∈ s₁ then hQ₁ a else (fun _ => (· = hh a)))
  constructor=> [|hv/= hh' /= H']
  { sby move=> ?? /=; scase_if }
  exists (fun _ => val_unit)=> /=; srw fun_insert_ss
  exists (fun a => if a ∈ s₂ then hQ₁ a else (fun _ => (· = hh' a)))
  constructor
  { move=> a /[dup]/dj/=; scase_if=> //== ??
    sby move: (H' a); scase_if=> // ? ->; apply hev }
  move=> hv' /=; srw -fun_insert_assoc
  apply hhimpl_trans_r; apply himp
  move=> hh /= /[swap] a /(_ a) /==
  sby move: (H' a); scase_if


/- **Focus** Rule -/

lemma heval_focus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) ->
  heval (s₁ ∪ s₂) hh ht hQ := by
  move=> /Set.disjoint_left dj ![hQ₁ hev] /= himp
  scase!: (heval_nonrel_sat hev)=> hh' hv H
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_=> //; scase: H=> hv' /= /heval_strongest ![hQ₂ hstr hev' /= himp']
  exists (fun a => if a ∈ s₁ then hQ₁ a else hQ₂ a)=> ⟨|⟩
  { apply heval_nonrel_split=> [a|a /[dup]?/dj] /=; scase_if=> //
    sby move: (hev' a)=> // }
  clear hv H himp'=> hv hh' /= H'
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_
  { sby move=> a; scase_if=> //; move: (H' a)=> /==; scase_if }
  scase: H=> hv'' ![hQ₂' hev /=]
  srw fun_insert_ss -fun_insert_assoc=> /(_ hv) /fun_insert_ff
  sapply=> a; scase_if=> //; rotate_left
  { sby move: (H' a)=> /==; scase_if }
  move: (H' a)=> /==; scase_if=> ?; scase_if=> // ??
  sby apply hstr=> // a /[dup]/dj ? /hev /=; scase_if


end heval


end HSepLog


/- ------------------ Function Substitution ------------------ -/
open Function (partialInv)

section hsubst

open Classical

variable {α β: Type}
variable (σ : α -> β)

def hlocal (s : Set α) (h : @hheap α) := ∀ a, a ∉ s -> h a = ∅
def hhlocal (s : Set α) (H : @hhProp α) := H ==> hlocal s

noncomputable def partialInvSet (s : Set α) (σ : α -> β) : β -> Option α :=
  fun b =>
    if h : ∃ a ∈ s, σ a = b then some (choose h) else none

noncomputable def fsubst {γ : Type} [Inhabited γ] (s : Set α) (g : α -> γ) : β -> γ :=
  fun b => (g <$> partialInvSet s σ b).get!

instance (priority := high) : Inhabited Prop := ⟨False⟩

@[inline] abbrev ssubst (s : Set α) : Set α -> Set β := fsubst σ s



variable (s : Set α)

def validSubst (g : α -> γ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, σ a = σ b -> g a = g b


lemma fsubst_inE :
  validSubst σ s s' ->
  (b ∈ ssubst σ s s' <-> ∃ x ∈ s ∩ s', σ x = b) := by
  move=> vs
  srw Membership.mem Set.instMembership Set.Mem ssubst fsubst=> /==
  unfold partialInvSet
  scase: [∃ x ∈ s, σ x = b]=> h
  { sby srw dif_neg /=; unfold default instInhabitedProp_lgtm }
  srw dif_pos=> //==; constructor=> [|[]x[][]]
  all_goals move: (choose_spec h)=> [] //
  sby move=> /vs h ? /h h *; srw h

@[simp]
lemma valisSubstss : validSubst σ s s = True := by
  sby move=> /== ?

lemma fsubst_in : a ∈ s -> σ a ∈ ssubst σ s s := by
  sby move=> ?; srw fsubst_inE

def hsubst (s : Set α) : @hhProp α -> @hhProp β :=
  fun H h =>
    ∃ h',
      h = fsubst σ s h' ∧
      H h' ∧
      validSubst σ s h'

lemma fsubst_σ [Inhabited γ] (f : α -> γ) :
  validSubst σ s f ->
  x ∈ s ->
  fsubst σ s f (σ x) = f x := by
  move=> vs xin; srw fsubst partialInvSet
  srw dif_pos
  { move=> /=; move: (?hc)=> /choose_spec => []??
    sby apply vs }
  sdone

lemma fsubst_heval_nonrel (s : Set α) :
  validSubst σ s hh ->
  validSubst σ s Q ->
  heval_nonrel (ssubst σ s s) (fsubst σ s hh) ht (fsubst σ s Q) ->
  heval_nonrel s hh (ht ∘ σ) Q := by
  move=> ?? ev a /= /[dup]? /(fsubst_in (σ := σ)) /ev
  sby srw ?fsubst_σ

lemma fsubst_comp_σ [Inhabited γ] (f : β -> γ) :
  ∀ x, x ∈ ssubst σ s s -> fsubst σ s (f ∘ σ) x = f x := by
  sby move=> x /fsubst_inE /== ?? <-; srw fsubst_σ

def injectiveSet (s : Set α) :=
  ∀ a ∈ s, ∀ b ∈ s, σ a = σ b -> a = b

@[simp]
lemma injectiveSet_validSubst {inj : injectiveSet σ s} :
  validSubst σ s f := by
  move=> ? /inj/[apply]/[apply]/[apply]->

lemma fsubst_out [Inhabited γ] (f : α -> γ) :
  a ∉ ssubst σ s s -> fsubst σ s f a = default := by
  srw fsubst_inE /== fsubst partialInvSet=> ?
  sby srw dif_neg

lemma fsubst_eq_local_eq [Inhabited γ] (f f' : α -> γ) :
  validSubst σ s f ->
  validSubst σ s f' ->
  fsubst σ s f = fsubst σ s f' -> ∀ a ∈ s, f a = f' a := by
    move=> ?? /[swap] a /(congr (a₁ := σ a) (a₂ := σ a)) /[swap] ?
    sby srw ?fsubst_σ

set_option maxHeartbeats 800000 in
lemma heval_hsubst (s : Set α) :
  injectiveSet σ s ->
  (∀ hv h, Q hv h -> ∀ a ∉ s, h a = hh a) ->
  -- (∀ hv hh₁ hh₂, (∀ a ∈ s, hh₁ a = hh₂ a) -> Q hv hh₁ = Q hv hh₂) ->
  heval (ssubst σ s s) (fsubst σ s hh) ht (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  heval s hh (ht ∘ σ) Q := by
  move=> vs Ql ![hQ ev himp]
  exists hQ ∘ σ; constructor
  { apply fsubst_heval_nonrel=> //
    apply heval_nonrel_conseq=> // ??
    sby srw fsubst_comp_σ }
  move=> hv /= h hQh
  move: (himp (fsubst σ s hv) (fsubst σ s h))
  shave H: bighstarDef (ssubst σ s s) (fun a ↦ hQ a (fsubst σ s hv a)) (fsubst σ s hh) (fsubst σ s h)
  { move=> a; scase_if
    { move=>/fsubst_inE /== a' ? <-
      sby move: (hQh a'); srw if_pos //= ?fsubst_σ }
    sby move=> ?; srw ?fsubst_out }
  move=> /(_ H) ![hv' h' /=] /fsubst_eq_local_eq heq hQ _
  let f := fun a => if σ a ∈ ssubst σ s s then fsubst σ s hv (σ a) else hv' (σ a)
  exists f=> /=
  shave->: (hv ∪_s f) = (fsubst σ s hv ∪_(ssubst σ s s) hv') ∘ σ
  { move=> !a /=; scase_if=> ain //
    sby (checkpoint srw if_pos // ?fsubst_σ //; apply fsubst_in) }
  shave-> //: h = h'
  move=> !a; scase: [a ∈ s]=> [|/heq//]
  sby move: (hQh a) hQ; scase_if=> // ? -> /Ql


end hsubst

/- ------------------ Evaluation of Hyper Programs ------------------ -/

section HEvalTrm

open trm eval

open Classical

lemma heval_seq :
  heval s hh ht₁ (fun _ h₂ => heval s h₂ ht₂ Q) ->
  heval s hh (fun d => trm_seq (ht₁ d) (ht₂ d)) Q := by
    scase! => hQ₁ hev₁ /= himp
    exists fun a v => hexists fun h' => hexists fun v' => hpure (hQ₁ a v' h') ∗ sP h' (ht₂ a) v
    constructor=> /==
    { move=> a /[dup] /hev₁ _ ain /= ⟨|//|⟩ v₂ h₂ ?
      move: (heval_nonrel_sat' hev₁)=> ![hh₂' hv₂' hQH₁ hheq]
      let hh₂ := fun b => if b = a then h₂ else hh₂' b
      let hv₂ := fun b => if b = a then v₂ else hv₂' b
      specialize himp hv₂ hh₂ ?_
      { sby move=> b /=; scase_if <;> simp [hv₂, hh₂] <;> scase_if }
      apply eval_conseq (Q1 := sP h₂ (ht₂ a))
      { sby scase: himp=> /= _ ![hQ /(_ ain)]; simp [hh₂]=> /sP_post }
      sby move=> v /=; xsimp }
    move=> hv; srw ?bighstarDef_hexists
    apply hhimpl_hhexists_l=> hh'
    apply hhimpl_hhexists_l=> hv'
    srw -(empty_hunion hh) -bighstarDef_hhstar; rotate_left
    { move=> ?; apply Finmap.disjoint_empty }
    erw [bighstarDef_hpure]
    apply hhimpl_hstar_hhpure_l=> hQ₁H
    specialize himp hv' (hh' ∪_s hh) ?_
    { sby move=> a; scase_if }
    scase: himp=> /= _ ![hQ /hstrongest_postP sPimp imp]
    apply hhimpl_trans_r; apply imp
    srw (bighstarDef_def_eq (h₀' := hh' ∪_s hh))=> //
    apply bighstarDef_himpl=> a /[dup]?/sPimp /(_ hv a)
    sby simp [hStrongestPostNonrel]; scase_if

lemma heval_let (x : α -> var) (ht₂ : α -> trm) :
  heval s hh ht₁ (fun hv h₂ => heval s h₂ (fun d => subst (x d) (hv d) (ht₂ d)) Q) ->
  heval s hh (fun d => trm_let (x d) (ht₁ d) (ht₂ d)) Q := by
    scase! => hQ₁ hev₁ /= himp
    exists fun a v =>
      hexists fun h' => hexists fun v' => hpure (hQ₁ a v' h') ∗ sP h' (subst (x a) v' (ht₂ a)) v
    constructor=> /==
    { move=> a /[dup] /hev₁ _ ain /= ⟨|//|⟩ v₂ h₂ ?
      move: (heval_nonrel_sat' hev₁)=> ![hh₂' hv₂' hQH₁ hheq]
      let hh₂ := fun b => if b = a then h₂ else hh₂' b
      let hv₂ := fun b => if b = a then v₂ else hv₂' b
      specialize himp hv₂ hh₂ ?_
      { sby move=> b /=; scase_if <;> simp [hv₂, hh₂] <;> scase_if }
      apply eval_conseq (Q1 := sP h₂ (subst (x a) v₂ (ht₂ a)))
      { scase: himp=> /= ? ![hQ /(_ (ain))]; simp [hh₂, hv₂]=> /sP_post
        sby srw ?if_pos }
      sby move=> v /=; xsimp }
    move=> hv; srw ?bighstarDef_hexists
    apply hhimpl_hhexists_l=> hh'
    apply hhimpl_hhexists_l=> hv'
    srw -(empty_hunion hh) -bighstarDef_hhstar; rotate_left
    { move=> ?; apply Finmap.disjoint_empty }
    erw [bighstarDef_hpure]
    apply hhimpl_hstar_hhpure_l=> hQ₁H
    specialize himp hv' (hh' ∪_s hh) ?_
    { sby move=> a; scase_if }
    scase: himp=> /= ? ![hQ /hstrongest_postP sPimp imp]
    apply hhimpl_trans_r; apply imp
    srw (bighstarDef_def_eq (h₀' := hh' ∪_s hh))=> //
    apply bighstarDef_himpl=> a /[dup]?/sPimp /(_ hv a)
    sby simp [hStrongestPostNonrel]; scase_if

open val

lemma heval_if (ht₁ ht₂ : htrm α) (s : Set α) (b : α -> Bool) :
  heval s h₁ (fun a => if b a then ht₁ a else ht₂ a) Q ->
  heval s h₁ (fun a => trm_if (val_bool (b a)) (ht₁ a) (ht₂ a)) Q := by
  sby scase! => * ⟨|⟨|⟩⟩

lemma heval_nonrel_ht_eq :
  heval_nonrel s h₁ ht₁ Q ->
  (∀ a ∈ s, ht₁ a = ht₂ a) ->
  heval_nonrel s h₁ ht₂ Q := by
  move=> hev eq a /[dup] ain
  sby move: (hev a ain)=> /eq

lemma heval_app_fun (s : Set α) (hv₁ : hval α) (x : α -> var) (ht₁ : α -> trm)
  (hv₂ : hval α ) :
  (forall d, d ∈ s -> hv₁ d = val_fun (x d) (ht₁ d)) ->
  heval s h₁ (fun a => subst (x a) (hv₂ a) (ht₁ a)) Q ->
  heval s h₁ (fun a => trm_app (hv₁ a) (hv₂ a)) Q := by
  move=> ? ![*]⟨|⟨|⟩⟩//
  apply heval_nonrel_ht_eq (ht₁ := fun a => trm_app (val_fun (x a) (ht₁ a)) (hv₂ a))=> //
  sby move=> ??; apply eval_app_fun

lemma heval_app_fix (s : Set α) (hv₁ : hval α) (x f : α -> var) (ht₁ : α -> trm)
  (hv₂ : hval α) :
  (forall d, d ∈ s -> hv₁ d = val_fix (f d) (x d) (ht₁ d)) ->
  heval s h₁ (fun a => subst (x a) (hv₂ a) $ subst (f a) (hv₁ a) $ ht₁ a) Q ->
  heval s h₁ (fun a => trm_app (hv₁ a) (hv₂ a)) Q := by
  move=> eq ![*]⟨|⟨|⟩⟩//
  apply heval_nonrel_ht_eq (ht₁ := fun a => trm_app (val_fix (f a) (x a) (ht₁ a)) (hv₂ a))=> //
  sby move=> ??; apply eval_app_fix=> //; srw -eq

lemma heval_val :
  heval s h (trm_val ∘ hv) (fun v h' => v = hv ∧ h = h') := by
  exists (fun a v h' => v = hv a ∧ h a = h'); constructor=> //
  { sdone }
  move=> hv' /= ? /= H ⟨//|⟩/= ⟨|⟩
  all_goals sby funext a; move: (H a); scase_if

lemma heval_fun (s : Set α) (x : α -> var) (ht₁ : α -> trm):
  heval s h (fun a => trm_fun (x a) (ht₁ a)) (fun hv h' => h = h' ∧ hv = fun a => val_fun (x a) (ht₁ a)) := by
  exists (fun a v h' => h a = h' ∧ v = val_fun (x a) (ht₁ a)); constructor=> //
  { sdone }
  move=> hv' /= ? /= H ⟨|⟨|⟩⟩/=; exact (fun a => val_fun (x a) (ht₁ a))
  all_goals sby funext a; move: (H a); scase_if

lemma heval_fix (s : Set α) (x f : α -> var) (ht₁ : α -> trm) :
  heval s h (fun a => trm_fix (f a) (x a) (ht₁ a)) (fun hv h' => h = h' ∧ hv = fun a => val_fix (f a) (x a) (ht₁ a)) := by
  exists (fun a v h' => h a = h' ∧ v = val_fix (f a) (x a) (ht₁ a)); constructor=> //
  { sdone }
  move=> hv' /= ? /= H ⟨|⟨|⟩⟩/=; exact (fun a => val_fix (f a) (x a) (ht₁ a))
  all_goals sby funext a; move: (H a); scase_if


end HEvalTrm

/- ================= Hyper Separation Logic Reasoning Rules ================= -/

/- -------------- Definition of Hyper Separation Logic Triples -------------- -/

section HTriple

variable {α : Type} (s : Set α)

section
local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α

abbrev htriple (t : htrm) (H : hhProp) (Q : hval → hhProp) : Prop :=
  forall hh, H hh → heval s hh t Q

/- -------------- Structural Rules -------------- -/

lemma htriple_conseq (t : htrm) (H H' : hhProp) (Q Q' : hval → hhProp) :
  htriple s t H Q →
  H' ==> H →
  Q ===> Q' →
  htriple s t H' Q' := by
  sby move=> htr himp ? ? /himp/htr/heval_conseq

attribute [simp] hqstarE

lemma htriple_frame (t : htrm) (H : hhProp) (Q : hval → hhProp) :
  htriple s t H Q →
  htriple s t (H ∗ H') (Q ∗ H') := by
  move=> htr hh ![hh hh' /htr/heval_frame hev ? -> /hev /heval_conseq]
  sapply=> ? /==
  -- TODO: xsimp
  sby apply hhimpl_hhstar_trans_r; rotate_left; apply hhimpl_refl


lemma htriple_hhexists (H : β -> hhProp) :
  (∀ x, htriple s t (H x) Q) →
  htriple s t (h∃ x, H x) Q := by
  sby move=> htr hh ![x /htr]

lemma htriple_hhpure :
  (P -> htriple s t H Q) →
  htriple s t (⌜P⌝ ∗ H) Q := by
  move=> htr hh ![> []/=/htr{}htr->/htr ?->]
  sby srw empty_hunion

lemma htriple_hhforall (J : β -> hhProp) :
  htriple s t (J x) Q ->
  htriple s t (h∀ x, J x) Q := by
  sby sdone

lemma htriple_hhwand_hhpure_l :
  P ->
  htriple s t H Q ->
  htriple s t (⌜P⌝ -∗ H) Q := by
  move=> ? htr hh ![> ?] ![]/= imp ->->?
  apply htr=> //; apply imp
  srw hunion_empty
  exists ∅, w_1; repeat' constructor=> //
  { srw empty_hunion }
  move=> ? /=; apply Finmap.disjoint_empty

lemma htriple_conseq_frame :
  htriple s t H₁ Q₁ →
  H ==> H₁ ∗ H₂ →
  Q₁ ∗ H₂ ===> Q →
  htriple s t H Q := by
  move=> htr himp qimp; eapply htriple_conseq; eapply htriple_frame
  hide_mvars; all_goals sdone

lemma htriple_ramified_frame :
  htriple s t H₁ Q₁ ->
  H ==> H₁ ∗ (Q₁ -∗ Q) ->
  htriple s t H Q := by
  move=> htr himp; eapply htriple_conseq_frame=> //
  sby srw -hqwand_equiv

lemma htriple_prod (H : α -> hProp) (Q : α -> val -> hProp) :
  (∀ a ∈ s, triple (ht a) (H a) (Q a)) ->
  htriple s ht [∗ i in s| H i] (fun hv => [∗ i in s| Q i (hv i)]) := by
    move=> htr hh hH; apply heval_prod
    { sby move=> a /[dup]?/htr; sapply; move: (hH a) }
    sby move=> a; move: (hH a)

end

lemma htriple_hsubst (ht : htrm β) (H : hhProp α) (Q : hval α -> hhProp α) (σ : α -> β) :
  injectiveSet σ s ->
  hhlocal s H ->
  (∀ hv, hhlocal s $ Q hv) ->
  htriple (ssubst σ s s) ht (hsubst σ s H) (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  htriple s (ht ∘ σ) H Q := by
  move=> inj Hl Ql htr hh Hh; apply heval_hsubst=>//
  { sby move=> ?? /Ql hl ? /[dup]/hl-> /(Hl _ Hh) }
  sby apply htr; exists hh

/- -------------- Rules for Hyper terms -------------- -/
section
local notation "htrm" => htrm α
local notation "hval" => hval α
local notation "hhProp" => hhProp α
open trm val prim

lemma htriple_val (Q : hval -> hhProp) :
  H ==> Q v ->
  htriple s (trm_val ∘ v) H Q := by
    move=> himp hh /himp ?; apply heval_conseq
    { sby apply heval_val }
    sby move=> >?

lemma htriple_fun (Q : hval -> hhProp) (x : α -> var) (ht : α -> trm) :
  (H ==> Q fun a => val_fun (x a) (ht a)) ->
  htriple s (fun a => trm_fun (x a) (ht a)) H Q := by
    move=> himp hh /himp ?; apply heval_conseq
    { sby apply heval_fun }
    sby move=> >?

lemma htriple_fix (Q : hval -> hhProp) (x f : α -> var) (ht : α -> trm) :
  (H ==> Q fun a => val_fix (f a) (x a) (ht a)) ->
  htriple s (fun a => trm_fix (f a) (x a) (ht a)) H Q := by
    move=> himp hh /himp ?; apply heval_conseq
    { sby apply heval_fix }
    sby move=> >?

lemma htriple_if (b : α -> Bool) (ht₁ ht₂ : α -> trm) (Q : hval -> hhProp) :
  htriple s (fun a => if b a then ht₁ a else ht₂ a) H Q ->
  htriple s (fun a => trm_if (val_bool (b a)) (ht₁ a) (ht₂ a)) H Q := by
    move=> htr hh /htr ?; apply heval_conseq
    { sby apply heval_if }
    sby move=> >?

lemma htriple_app_fun (Q : hval -> hhProp) (hv₁ : hval) (x : α -> var) (ht₁ : α -> trm) (hv₂ : hval) :
  (forall d, d ∈ s -> hv₁ d = val_fun (x d) (ht₁ d)) ->
  htriple s (fun a => subst (x a) (hv₂ a) (ht₁ a)) H Q ->
  htriple s (fun a => trm_app (hv₁ a) (hv₂ a)) H Q := by
    move=> eq htr hh /htr ?; apply heval_conseq
    { sby apply heval_app_fun }
    sby move=> >?

lemma htriple_app_fix (Q : hval -> hhProp) (hv₁ : hval) (x f : α -> var) (ht₁ : α -> trm) (hv₂ : hval) :
  (forall d, d ∈ s -> hv₁ d = val_fix (f d) (x d) (ht₁ d)) ->
  htriple s (fun a => subst (x a) (hv₂ a) $ subst (f a) (hv₁ a) $ ht₁ a) H Q ->
  htriple s (fun a => trm_app (hv₁ a) (hv₂ a)) H Q := by
    move=> eq htr hh /htr ?; apply heval_conseq
    { sby apply heval_app_fix }
    sby move=> >?

/- -------------- Hyper Triple-Style Specification for Primitive Hyper Functions -------------- -/

notation (priority := high) "funloc" p "=>" H => fun hv => h∃ p, ⌜ hv = val_loc ∘ p ⌝ ∗ H

open Classical

lemma htriple_ref' (v : α -> val) :
  htriple s (fun a => trm_app val_ref (v a))
    emp
    (fun hv => [∗ i in s| hexists fun p => hpure (hv i = val_loc p) ∗ p ~~> v i]) := by
    srw -(bighstar_hhempty (s := s)); apply htriple_prod (Q := fun a v' => hexists fun p => hpure (v' = val_loc p) ∗ p ~~> v a)
    move=> ??; apply triple_ref

lemma htriple_hv_ext :
  htriple s ht H (fun hv => h∃ hv', Q (hv ∪_s hv')) ->
  htriple s ht H Q := by
  move=> htr ? /htr ![hQ ? imp] ⟨//|⟨//|?⟩⟩
  apply hhimpl_trans=> //=
  -- TODO: xsimp
  apply hhimpl_hhexists_l=> hv'
  apply hhimpl_hhexists_l=> hv''
  apply hhimpl_hhexists_r (x := hv'')
  sby srw fun_insert_ss


lemma htriple_ref (v : α -> val) :
  htriple s (fun a => trm_app val_ref (v a))
    emp
    (funloc p => [∗ i in s| p i ~~> v i]) := by
    apply htriple_hv_ext
    apply htriple_conseq; apply htriple_ref'; apply hhimpl_refl
    move=> hv /=; srw bighstar_hexists
    -- TODO: xsimp
    apply hhimpl_hhexists_l=> p
    apply hhimpl_hhexists_r (x := val_loc ∘ p)
    apply hhimpl_hhexists_r (x := p)
    srw -bighstar_hhstar bighstar
    erw [(bighstarDef_hpure (P := fun i => hv i = val_loc (p i)))]
    -- TODO: xsimp
    apply hhimpl_frame_l
    move=> h [] /= p -> ⟨ /= |//⟩
    sby funext x

lemma htriple_prod_val_eq (ht : htrm) (H : α -> _) (Q : α -> _) (fv : hval) :
  (∀ a ∈ s, triple (ht a) (H a) (fun v => hpure (v = fv a) ∗ Q a)) ->
  htriple s ht [∗ i in s| H i] (fun hv => ⌜hv = fv⌝ ∗ [∗ i in s| Q i]) := by
  move=> htr
  shave htr: htriple s ht [∗ i in s| H i] (fun hv => [∗ i in s| hpure (hv i = fv i) ∗ Q i])
  { sby apply htriple_prod (Q := fun a v' => hpure (v' = fv a) ∗ Q a) }
  apply htriple_hv_ext
  apply htriple_conseq; apply htr; apply hhimpl_refl
  move=> hv /=
  apply hhimpl_hhexists_r (x := fv)
  srw -bighstar_hhstar bighstar
  erw [(bighstarDef_hpure (P := fun i => hv i = fv i))]
  apply hhimpl_frame_l
  move=> h [] /= p -> ⟨ /= |//⟩
  sby funext x

lemma htriple_prod_val_eq_emp (ht : htrm) (fv : hval) :
  (∀ a ∈ s, triple (ht a) hempty (fun v => hpure (v = fv a))) ->
  htriple s ht emp (fun hv => ⌜hv = fv⌝) := by
  move: (htriple_prod_val_eq s ht (fun _ => hempty) (fun _ => hempty) fv)
  move=> H htr; apply htriple_conseq; apply H=> //
  { move=> ??; apply triple_conseq=> // ? /=; xsimp }
  { sby srw bighstar_hhempty }
  move=> ? /= -- TODO: xsimp
  sby srw bighstar_hhempty hhstar_hhempty_r

lemma htriple_get (p : α -> loc) :
  htriple s (fun a => trm_app val_get (val_loc (p a)))
    [∗ i in s| p i ~~> v i]
    (fun hv => ⌜hv = v⌝ ∗ [∗ i in s| p i ~~> v i]) := by
    apply htriple_prod_val_eq=> *; apply triple_get

lemma htriple_set (hv hu : hval) (p : α -> loc) :
  htriple s (fun a => trm_app (trm_app val_set (p a)) (hu a))
    [∗ i in s| p i ~~> hv i]
    (fun hv => ⌜hv = fun _ => val_unit⌝ ∗ [∗ i in s| p i ~~> hu i]) := by
    apply htriple_prod_val_eq
    move=> ??; apply triple_set

lemma htriple_free (hv : hval) (p : α -> loc) :
  htriple s (fun a => trm_app val_free (val_loc (p a)))
    [∗ i in s| p i ~~> hv i]
    (fun _ => emp) := by
    srw -(bighstar_hhempty (s := s))
    apply htriple_prod (Q := fun _ _ => hempty)
    move=> ??; apply triple_free

lemma htriple_unop (op : α -> prim) (v₁ v : hval) :
  (∀ a ∈ s, evalunop (op a) (v₁ a) (· = v a)) ->
  htriple s (fun a => trm_app (op a) (v₁ a))
    emp
    (fun hv => ⌜hv = v⌝) := by
    move=> ?; apply htriple_prod_val_eq_emp=> ??
    sby apply triple_unop

lemma htriple_binop (op : α -> prim) (v₁ v₂ v : hval) :
  (∀ a ∈ s, evalbinop (op a) (v₁ a) (v₂ a) (· = v a)) ->
  htriple s (fun a => trm_app (op a) (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = v⌝) := by
    move=> ?; apply htriple_prod_val_eq_emp=> ??
    sby apply triple_binop

lemma htriple_add (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_add (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i + v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_div (v₁ v₂ : α -> Int) :
  (∀ a ∈ s, v₂ a ≠ 0) ->
  htriple s (fun a => trm_app val_div (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i / v₂ i⌝) := by
  sby move=> neq; apply htriple_binop=> ? /neq

lemma htriple_neg (v₁ : α -> Bool) :
  htriple s (fun a => trm_app val_neg (v₁ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ ¬v₁ i⌝) := by
  sby apply htriple_unop

lemma htriple_opp (v₁ : α -> Int) :
  htriple s (fun a => trm_app val_opp (v₁ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ -v₁ i⌝) := by
  sby apply htriple_unop

lemma htriple_eq (v₁ v₂ : α -> val) :
  htriple s (fun a => trm_app val_eq (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i = v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_neq (v₁ v₂ : α -> val) :
  htriple s (fun a => trm_app val_neq (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ is_true $ v₁ i ≠ v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_sub (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_sub (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i - v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_mul (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_mul (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i * v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_mod (v₁ v₂ : α -> Int) :
  (∀ a ∈ s, v₂ a ≠ 0) ->
  htriple s (fun a => trm_app val_mod (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i % v₂ i⌝) := by
  sby move=> neq; apply htriple_binop=> ? /neq

lemma htriple_le (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_le (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i ≤ v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_lt (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_lt (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i < v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_ge (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_ge (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i ≥ v₂ i⌝) := by
  sby apply htriple_binop


lemma htriple_gt (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_gt (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i > v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_ptr_add (v₁ : α -> loc) (v₂ : α -> Int) :
  (∀ i ∈ s, v₁ i + v₂ i >= 0) ->
  htriple s (fun a => trm_app val_ptr_add (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_loc $ (v₁ i + v₂ i).natAbs⌝) := by
  sby move=> imp; apply htriple_prod_val_eq_emp=> ? /imp ?
      apply triple_ptr_add

end
end HTriple

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
  -- xsimp
  sorry


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
  -- xchange
  sorry

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
