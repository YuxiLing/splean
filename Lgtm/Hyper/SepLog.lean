-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange

import Lgtm.Common.State

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
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv')
    /-                    hQ'                      ==>         hQ -/

/- -------------- Hyper-Evaluation Properties -------------- -/

/- **Frame** Rule -/
lemma heval_nonrel_conseq (s : Set α) :
  heval_nonrel s hh t Q1 →
  (∀ a ∈ s, qimpl (Q1 a) $ Q2 a) →
  heval_nonrel s hh t Q2 := by
  sby move=> hev qimp a /[dup] ain/hev/eval_conseq /(_ (qimp a ain))

lemma heval_conseq' :
  heval s hh t Q1 →
  Q1 ===> (∃ʰ hv : hval, Q2 $ · ∪_s hv) →
  heval s hh t Q2 := by
  scase! => ?? himp qimp ⟨//|⟩
  constructor=> // hv
  ychange himp=> ?; ychange qimp=> ?
  srw fun_insert_ss; ysimp


lemma heval_conseq :
  heval s hh t Q1 →
  Q1 ===> Q2 →
  heval s hh t Q2 := by
  scase! => ?? himp qimp ⟨//|⟩
  sby constructor=> // hv ? /himp; apply hhimpl_hhexists

abbrev tohhProp (f : hheap -> Prop) : hhProp := f

lemma heval_nonrel_frame :
  heval_nonrel s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval_nonrel s (hh1 ∪ hh2) t (fun a => Q a ∗ (tohProp (fun hh ↦ hh = hh2 a))) := by
  sby move=> hev ?? /hev /eval_frame



lemma heval_frame :
  heval s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval s (hh1 ∪ hh2) t (Q ∗ (tohhProp (· = hh2))) := by
  scase! => hQ ? himp ?
  exists fun a => hQ a ∗ (tohProp (· = hh2 a))=> ⟨|hv⟩
  { sby apply heval_nonrel_frame }
  srw qstarE hqstarE -bighstarDef_hhstar // bighstarDef_eq
  srw -hhstar_hhexists_l
  sby apply hhimpl_hhstar_trans_l

def hlocal (s : Set α) (h : hheap) := ∀ a, a ∉ s -> h a = ∅
def hhlocal (s : Set α) (H : hhProp) := H ==> hlocal s

@[simp]
lemma hhlocal_bighstar  :
  (hhlocal s (bighstar s' H)) = (s' ⊆ s) := by sorry

@[simp↓]
lemma hhlocal_hhadd [PartialCommMonoid val] :
  (hhlocal s (H₁ + H₂)) = (hhlocal s H₁ ∧ hhlocal s H₂) := by sorry

open EmptyPCM in
@[simp]
lemma hhlocal_hhstar  :
  (hhlocal s (H₁ ∗ H₂)) = (hhlocal s H₁ ∧ hhlocal s H₂) := by
  simp [<-hhaddE]

@[simp]
lemma hhlocal_hhexists  :
  (hhlocal s (hhexists H)) = ∀ x, hhlocal s (H x) := by sorry


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

abbrev ishsP (s : Set α) h t (sP : α -> _) :=
  ∀ Q, heval_nonrel s h t Q -> ∀ a ∈ s, qimpl (sP a) (Q a)

abbrev hsP (hh : hheap) (ht : htrm) :=
  fun a => sP (hh a) (ht a)


lemma hstrongest_postP :
  ishsP s hh ht (hsP hh ht) := by
  move=> Q ? a ?? /=; apply himpl_hforall_l _ (Q a)
  sby srw hwand_hpure_l


lemma hstrongest_post_provable :
  heval_nonrel s hh ht hQ -> heval_nonrel s hh ht (hsP hh ht) := by
  move=> hev a /hev; unfold hsP
  apply sP_post

lemma heval_strongest :
  heval s hh ht hQ ->
  ∃ (hQ' : α -> val -> hProp),
    ishsP s hh ht hQ' ∧
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv') := by
  scase! => hQ ? himp; exists hsP hh ht
  repeat' constructor
  { sby apply hstrongest_postP }
  { sby apply hstrongest_post_provable }
  move=> hv; apply hhimpl_trans_r; apply himp
  apply bighstarDef_himpl=> ??
  sby apply hstrongest_postP

lemma heval_strongest' :
  heval s hh ht hQ ->
    heval_nonrel s hh ht (hsP hh ht) ∧
    ∀ hv, bighstarDef s (fun a => hsP hh ht a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv') := by
  scase! => hQ ? himp
  repeat' constructor
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

lemma heval_ht_imp :
  (Set.EqOn ht₁ ht₂ s) ->
  heval s hh ht₁ hQ -> heval s hh ht₂ hQ := by
  sby move=> hteq ![*] ⟨|⟨? /[dup]/hteq<-|⟩⟩

lemma heval_ht_eq :
  (Set.EqOn ht₁ ht₂ s) ->
  heval s hh ht₁ hQ = heval s hh ht₂ hQ := by
  sby move=> hteq; apply propext=> ⟨|⟩ <;> apply heval_ht_imp

-- lemma heval_nonrel_frame_in :
--   hlocal s' hh' ->
--   Disjoint s s' ->
--   heval_nonrel s (hh ∪ hh') ht (fun a => hQ a ∗ (tohProp (· = hh' a))) ->
--   heval_nonrel s hh ht hQ := by
--   move=> hl /Set.disjoint_left dj /[swap] a /[swap] ain /(_ (ain)) /=
--   srw hl //== => ?; apply eval_conseq=> // hv /= ? ![> ? -> _ -> //]

lemma heval_nonrel_frame_in :
  hlocal s' hh' ->
  Disjoint s s' ->
  heval_nonrel s (hh ∪ hh') ht hQ ->
  heval_nonrel s hh ht hQ := by
  move=> hl /Set.disjoint_left dj /[swap] a /[swap] ain /(_ (ain)) /=
  srw hl //==

lemma heval_frame_in :
  hlocal s' hh' ->
  hhlocal s' H' ->
  (∀ hv, hhlocal s (hQ hv)) ->
  Disjoint s s' ->
  hlocal s hh ->
  heval s (hh ∪ hh') ht (hQ ∗ H') ->
  heval s hh ht hQ := by
  move=> hl hhl ql /[dup] /Set.disjoint_left ? dj hdj ![Q /heval_nonrel_frame_in hev himpl] ⟨//|⟨//|hv⟩⟩
  move=> h Hh
  specialize himpl hv (h ∪ hh') ?_
  { move=> a; scase_if=> ? /==;
    { srw hl //==
      move: (Hh a); srw if_pos //= }
    move: (Hh a); srw if_neg // }
  scase: himpl=> hv /= ![hh₁ hh₂ /= hQ hH' heq ?]
  exists hv=> /=
  shave-> //: h = hh₁
  move=> !a; move: heq
  srw funext_iff=> /(_ a) /=; scase: [a ∈ s]=> ?
  { move=> _; move: (Hh a); srw if_neg // => ->
    srw hdj // (ql _ _ hQ) // }
  srw hl // (hhl _ hH') //

end heval


end HSepLog

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
    sby simp [hsP]; scase_if

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
    sby simp [hsP]; scase_if

lemma heval_for (n₁ n₂ : α -> Int) (ht : α -> trm) (vr : α -> var) :
  (∀ a ∈ s, n₁ a < n₂ a) ->
  heval s hh (fun a => trm_seq (subst (vr a) (n₁ a) (ht a))
                               (trm_for (vr a) (val.val_int $ n₁ a + 1) (n₂ a) (ht a))) Q ->
  heval s hh (fun a => trm_for (vr a) (n₁ a) (n₂ a) (ht a)) Q := by
  sby move=> ? ![*]⟨|⟨??⟨⟩|//⟩⟩; srw if_pos

-- lemma heval_while' (cnd ht : α -> trm) :
--   heval s hh (fun a => (cnd a).trm_if ((ht a).trm_seq (trm_while (cnd a) (ht a))) val.val_unit) Q ->
--   heval s hh (fun a => trm_while (cnd a) (ht a)) Q := by
--   sby move=> ![*]⟨|⟨??⟨⟩|//⟩⟩

lemma heval_while (cnd ht : α -> trm) :
  (heval s hh cnd fun hv hh =>
    heval s hh (fun a => (trm_val $ hv a).trm_if ((ht a).trm_seq (trm_while (cnd a) (ht a))) val.val_unit) Q) ->
  heval s hh (fun a => trm_while (cnd a) (ht a)) Q := by
  scase! => hQ₁ hev₁ /= himp
  exists fun a v =>
    hexists fun h' => hexists fun v' => hpure (hQ₁ a v' h') ∗ sP h'
      (trm_if v' (trm_seq (ht a)  (trm_while (cnd a) (ht a))) (val.val_unit)) v
  constructor=> /==
  { move=> a /[dup] /hev₁ _ ain /= ⟨|//|⟩ h₂ v₂ ?
    move: (heval_nonrel_sat' hev₁)=> ![hh₂' hv₂' hQH₁ hheq]
    let hh₂ := fun b => if b = a then h₂ else hh₂' b
    let hv₂ := fun b => if b = a then v₂ else hv₂' b
    specialize himp hv₂ hh₂ ?_
    { sby move=> b /=; scase_if <;> simp [hv₂, hh₂] <;> scase_if }
    apply eval_conseq (Q1 := sP h₂ (trm_if v₂ (trm_seq (ht a) (trm_while (cnd a) (ht a))) val.val_unit))
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
  sby simp [hsP]; scase_if


lemma heval_for' (n₁ n₂ : α -> Int) (ht : α -> trm) (vr : α -> var) (Q : hval α -> hhProp α) :
  (∀ a ∈ s, n₁ a ≥ n₂ a) ->
  Q (fun _ => val.val_unit) hh ->
  heval s hh (fun a => trm_for (vr a) (n₁ a) (n₂ a) (ht a)) Q := by
  move=> ge ![*]⟨|⟨? ain⟨⟩|//⟩⟩
  { exact fun a v h => v = val.val_unit ∧ h = hh a }
  { srw if_neg=> // }
  move=> hv; ysimp=> hh' /= eq
  shave->: hh' = hh;
  { funext a; move: (eq a); scase_if=> // }
  shave->//: (hv ∪_s fun _ => val.val_unit) = fun _ => val.val_unit
  sby move=> !x /==; move: (eq x)







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

/- def heval (s : Set α) (hh : hheap) (ht : htrm) (hQ : hval -> hhProp) : Prop :=
   ∃ (hQ' : α -> val -> hProp),
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> ∃ʰ hv', hQ (hv ∪_s hv') -/

def fresh_ptr (s : state) : loc :=
  match s.keys.max with
  | ⊥      => 1
  | some n => n + 1

theorem fresh_ptr_sound (s : state) :
  fresh_ptr s ∉ s :=
by
  unfold fresh_ptr
  cases eqn:(s.keys.max)=> /=
  { move: eqn=> /Finset.max_eq_bot
    sby srw Not -Finmap.mem_keys }
  move: eqn=> /Finset.not_mem_of_max_lt
  sby srw -Finmap.mem_keys

lemma mem_exists_union (p : loc) (h : state) :
  p ∈ h →
  ∃ v, h = Finmap.singleton p v ∪ (h.erase p) := by
  move=> /Finmap.mem_iff [v] ?
  exists  v=> /==
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    sby srw Finmap.lookup_union_right }
  move=> ->
  sby srw Finmap.lookup_union_left

lemma hwand_pointer_erase :
  p ∈ h →
  H h →
  (hexists fun u ↦ p ~~> u -∗ H) (h.erase p) := by
  move=> /mem_exists_union [v] heq ?
  srw hwandE
  exists v=> /=
  exists (fun h' ↦ Finmap.singleton p v ∪ h' = h)=> /=
  srw hstar_hpure_r=> ⟨//|⟩
  sby move=> s ![>] /hsingl_inv -> /= -> ? ->

instance : HStar hProp (heap → Prop) hProp where
  hStar := hstar

/- def heval_nonrel (s : Set α) (hh : hheap) (ht : htrm) (hQ : α -> val -> hProp) : Prop :=
  ∀ a ∈ s, eval (hh a) (ht a) (hQ a) -/
lemma heval_ref (x : α → var) (hh : α → heap) (hv : α → val) (ht : α → trm) :
  (∀ (hp : α → loc), (∀ i ∈ s, hp i ∉ hh i) →
    heval s (fun i ↦ if i ∈ s then (hh i).insert (hp i) (hv i) else hh i) -- ∪_s
      (fun d ↦ subst (x d) (hp d) (ht d)) (Q ∗ ∃ʰ (hu : α → val), hp i ~⟨i in s⟩~> hu i )) →
  heval s hh (fun d ↦ trm_ref (x d) (hv d) (ht d)) Q :=
by
  move=> h
  exists (fun a v ↦ hexists fun p ↦ hpure (p ∉ hh a) ∗
    (hexists fun u ↦ p ~~> u -∗ sP ((hh a).insert p (hv a)) (subst (x a) p (ht a)) v))
  /- maybe should be something like:
     fun a v ↦ ∃ʰ p, ⌜p ∉ hh a⌝ ∗
      fun h ↦ ⌜p ∉ h⌝ ∗ ∃ʰ u, (sP ...) v (h.insert p u)
    obviously not correct notation but something similar might work.
   -/
  -- exists fun a v ↦ hexists fun p ↦ (hpure (p ∉ hh a)) ∗ fun (h : heap) ↦ p ∉ h ∧
  --   ∃ u, (sP ((hh a).insert p (hv a)) (subst (x a) p (ht a))) v (h.insert p u)
  constructor=> /==
  { move=> /== > /[dup] ain ?
    apply (eval.eval_ref _ _ _ _ _ (fun v s ↦ v = hv a ∧ s = hh a ))=> //
    move=> > [-> ->] > ?
    let hp (d : α) := if d = a then p else fresh_ptr (hh d)
    have hin:(∀ i ∈ s, hp i ∉ hh i) := by
      { move=> > _ ; srw hp
        scase_if=> // _ ; apply fresh_ptr_sound }
    apply h in hin=> {h} ![hQ' hev himp]
    move: (heval_nonrel_sat' hev)=> ![hh₂' hv₂' hQH₁ hheq]
    have hheq':(∀ a ∉ s, hh₂' a = hh a) := by
      { move=> > /[dup] ? /hheq ; sby scase_if }
    move=> {hheq}
    specialize hev a ; apply hev in ain=> /== ; scase_if=> // _
    srw hp=> /= {}hev
    apply (eval_conseq (Q1 := sP (Finmap.insert p (hv a) (hh a)) (subst (x a) p (ht a))))
    { sby apply sP_post }
    move=> v h /= hsP
    exists p=> /==
    srw hstar_hpure_l=> ⟨//|⟩
    apply hwand_pointer_erase=> //
    sorry }
  move=> hv' ; srw ?bighstarDef_hexists
  apply hhimpl_hhexists_l=> hp
  srw -(empty_hunion hh) -bighstarDef_hhstar; rotate_left
  { move=> ?; apply Finmap.disjoint_empty }
  erw [bighstarDef_hpure] ; srw empty_hunion
  apply hhimpl_hstar_hhpure_l=> /h {h} ![hQ' /hstrongest_postP sPimp /= himp]
  specialize himp hv'
  sorry

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
  sapply; ysimp=> //

lemma htriple_hhexists (H : β -> hhProp) :
  (∀ x, htriple s t (H x) Q) →
  htriple s t (∃ʰ x, H x) Q := by
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

lemma hhlocal_mem  (hh : hheap α):
  hlocal s hh ->
  x ∈ (hh a) -> a ∈ s := by sorry

lemma htriple_frame_in :
  hhlocal s' H' ->
  hhlocal s H ->
  (∀ (hv : hval), hhlocal s (Q hv)) ->
  Disjoint s s' ->
  (∃ hh', H' hh') ->
  (htriple s t (H ∗ H') (Q ∗ H') <->
  htriple s t H Q) := by
  move=> hl' hl ? /[dup]? /Set.disjoint_left dj [hh' Hh'] /== ⟨|⟩
  { move=> /[swap] hh /(_ (hh ∪ hh')) himpl Hh
    specialize himpl ?_
    { exists hh, hh'=> ⟨//|⟨//|⟨//|⟩⟩⟩ ?? /hhlocal_mem /(_ (hl _ Hh)) /[swap]
      move=> /hhlocal_mem  /(_ (hl' _ Hh')) // }
    apply heval_frame_in=> // }
  apply htriple_frame

open Classical in
lemma htriple_extend_univ (Q : hval -> hhProp) (H' : hProp) :
  s.Nonempty ->
  hhlocal s H ->
  (∀ (hv : hval), hhlocal s (Q hv)) ->
  htriple s t (H ∗ [∗ in Set.univ | H']) (Q ∗ [∗ in @Set.univ α | H']) =
  htriple s t (H ∗ [∗ in s| H']) (Q ∗ [∗ in s| H']) := by
  scase: [∃ h, H' h]=> /==
  { move=> unsat [a ain] * ⟨|⟩ ?? ![] >? /(_ a); srw if_pos// }
  move=> h ? _ ??
  srw (bighstarDef_univ_split (s := s))
  srw -[2](htriple_frame_in (H' := [∗ in sᶜ| H']) (s' := sᶜ))=> //
  { congr! 1=> [|!hv /=] <;> ysimp <;> ysimp }
  { exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a ↦ a }
  exists (fun a => if a ∉ s then h else ∅)=> a /=
  scase: [a ∈ sᶜ]=> /== //

end

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

notation (priority := high) "funloc" p "=>" H => fun hv => ∃ʰ p, ⌜ hv = val_loc ∘ p ⌝ ∗ H

open Classical

-- lemma htriple_ref' (v : α -> val) :
--   htriple s (fun a => trm_app val_ref (v a))
--     emp
--     (fun hv => [∗ i in s| hexists fun p => hpure (hv i = val_loc p) ∗ p ~~> v i]) := by
--     srw -(bighstar_hhempty (s := s)); apply htriple_prod (Q := fun a v' => hexists fun p => hpure (v' = val_loc p) ∗ p ~~> v a)
--     move=> ??; apply triple_ref

lemma htriple_hv_ext :
  htriple s ht H (fun hv => ∃ʰ hv', Q (hv ∪_s hv')) ->
  htriple s ht H Q := by
  move=> htr ? /htr ![hQ ? imp] ⟨//|⟨//|?⟩⟩
  apply hhimpl_trans=> //=
  ypull=> ? hv'; ysimp[hv']
  sby srw fun_insert_ss


-- lemma htriple_ref (v : α -> val) :
--   htriple s (fun a => trm_app val_ref (v a))
--     emp
--     (funloc p =>  p i ~⟨i in s⟩~> v i) := by
--     apply htriple_hv_ext
--     apply htriple_conseq; apply htriple_ref'; apply hhimpl_refl
--     move=> hv /=; srw bighstar_hexists
--     ypull=> p;
--     srw -bighstar_hhstar bighstar
--     erw [(bighstarDef_hpure (P := fun i => hv i = val_loc (p i)))]
--     ysimp[val_loc ∘ p, p]=> //
--     sby funext x

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
  move=> ? /=
  ysimp=> //

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

-- lemma htriple_free (hv : hval) (p : α -> loc) :
--   htriple s (fun a => trm_app val_free (val_loc (p a)))
--     [∗ i in s| p i ~~> hv i]
--     (fun _ => emp) := by
--     srw -(bighstar_hhempty (s := s))
--     apply htriple_prod (Q := fun _ _ => hempty)
--     move=> ??; apply triple_free

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

lemma htriple_addr (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_add (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_real $ r₁ i + r₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_div (v₁ v₂ : α -> Int) :
  (∀ a ∈ s, v₂ a ≠ 0) ->
  htriple s (fun a => trm_app val_div (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i / v₂ i⌝) := by
  sby move=> neq; apply htriple_binop=> ? /neq

lemma htriple_divr (r₁ r₂ : α -> ℝ) :
  (∀ a ∈ s, r₂ a ≠ 0) ->
  htriple s (fun a => trm_app val_div (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_real $ r₁ i / r₂ i⌝) := by
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

lemma htriple_oppr (r₁ : α -> ℝ) :
  htriple s (fun a => trm_app val_opp (val_real (r₁ a)))
    emp
    (fun hv => ⌜hv = fun i => val_real $ -r₁ i⌝) := by
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

lemma htriple_subr (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_sub (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_real $ r₁ i - r₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_mul (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_mul (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_int $ v₁ i * v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_mulr (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_mul (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_real $ r₁ i * r₂ i⌝) := by
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

lemma htriple_ler (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_le (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ r₁ i ≤ r₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_lt (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_lt (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i < v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_ltr (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_lt (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ r₁ i < r₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_ge (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_ge (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i ≥ v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_ger (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_ge (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ r₁ i ≥ r₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_gt (v₁ v₂ : α -> Int) :
  htriple s (fun a => trm_app val_gt (v₁ a) (v₂ a))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ v₁ i > v₂ i⌝) := by
  sby apply htriple_binop

lemma htriple_gtr (r₁ r₂ : α -> ℝ) :
  htriple s (fun a => trm_app val_gt (val_real (r₁ a)) (val_real (r₂ a)))
    emp
    (fun hv => ⌜hv = fun i => val_bool $ r₁ i > r₂ i⌝) := by
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
