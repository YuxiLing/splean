-- import Ssreflect.Lang
import Mathlib.Data.Finmap

-- lemmas about big operators
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp
import Lgtm.Unary.SepLog

import Lgtm.Hyper.HProp
import Lgtm.Hyper.YSimp
import Lgtm.Hyper.YChange
import Lgtm.Hyper.SepLog
import Lgtm.Hyper.WP

instance : Zero (hhProp α) where zero := emp

instance : Add (hhProp α) where add s t := s ∗ t

@[simp]
lemma hhProp_add_def (s t : hhProp α) : s + t = s ∗ t := rfl

@[simp]
lemma hhProp_zero_def : (0 : hhProp α) = emp := rfl

instance : Zero hProp where zero := hempty

instance : Add hProp where add s t := s ∗ t

@[simp]
lemma hProp_add_def (s t : hProp) : s + t = s ∗ t := rfl

@[simp]
lemma hProp_zero_def : 0 = hempty := rfl


instance : AddCommMonoid (hhProp α) where
  nsmul := nsmulRec
  add_assoc := by move=> > /==; srw hhstar_assoc
  zero_add  := by move=> > /==; srw hhstar_hhempty_l
  add_zero  := by intros; simp; apply hhstar_hhempty_r
  add_comm  := by intros; simp; apply hhstar_comm

attribute [-simp] hhProp_add_def

instance : AddCommMonoid hProp where
  nsmul := nsmulRec
  add_assoc := by move=> > /==; srw hstar_assoc
  zero_add  := by move=> > /==; srw hstar_hempty_l
  add_zero  := by intros; simp; apply hstar_hempty_r
  add_comm  := by intros; simp; apply hstar_comm

/- ------------------ Function Substitution ------------------ -/
open Function (partialInv)

section hsubst

open Classical

variable {α β: Type}
variable (σ : α -> β)


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

set_option maxHeartbeats 800000 in
lemma hsubst_heval (s : Set α) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  validSubst σ s hh ->
  hlocal s hh ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  heval s hh (ht ∘ σ) Q ->
  heval (ssubst σ s s) (fsubst σ s hh) ht (fun hv => hsubst σ s (Q (hv ∘ σ))) := by
  move=> σP vs hl Qeq /heval_strongest' ![hev himp]
  shave vsP: validSubst σ s (hsP hh (ht ∘ σ))
  { move; simp [hsP]=> ???? /[dup] /vs->// }
  exists fsubst σ s (hsP hh (ht ∘ σ))=> ⟨b/fsubst_inE //==![a ain <-]|⟩
  { sby srw ?fsubst_σ }
  move=> hv h hP; move: (himp (hv ∘ σ) (h ∘ σ))=> Hex
  specialize Hex ?_
  { move=> a; move: (hP (σ a))
    srw fsubst_inE /==; scase: [a ∈ s]=> /= ?
    { srw if_neg // fsubst_out ?fsubst_inE //= hl // }
    srw if_pos // fsubst_σ // }
  scase: Hex=> hv' /= QP
  exists fsubst σ s hv'=> /=
  exists (h ∘ σ)=> ⟨!b|⟨|⟩⟩//
  { scase: [b ∈ ssubst σ s s]
    { move=> bout; srw fsubst_out //
      scase: (bighstarDef_split _ _ hP)=> _ /(_ (bout)) ->
      sby srw fsubst_out }
    sby move=>/fsubst_comp_σ }
  srw Qeq //= => a /== /[dup] /fsubst_in/(_ σ) * //

lemma htriple_hsubst (ht : htrm β) (H : hhProp α) (Q : hval α -> hhProp α) (σ : α -> β) :
  injectiveSet σ s ->
  hhlocal s H ->
  (∀ hv, hhlocal s $ Q hv) ->
  htriple (ssubst σ s s) ht (hsubst σ s H) (fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  htriple s (ht ∘ σ) H Q := by
  move=> inj Hl Ql htr hh Hh; apply heval_hsubst=>//
  { sby move=> ?? /Ql hl ? /[dup]/hl-> /(Hl _ Hh) }
  sby apply htr; exists hh

set_option maxHeartbeats 800000 in
lemma hsubst_bighstar (σ : β -> α)
  (s s' : Set β) (H : α -> hProp) :
  (∀ᵉ (a ∈ s') (a' ∉ s'), σ a ≠ σ a') ->
  s' ⊆ s ->
  validSubst σ s s' ->
  hsubst σ s [∗ i in s' | H (σ i)] =
  [∗ i in ssubst σ s s' | H i] := by
  move=> σP ?? !h !⟨![h ->]|⟩
  { move=> hP vs a /=; srw fsubst_inE // Set.inter_eq_self_of_subset_right //
    scase_if=> [/== b ?<-|/== bin]
    { move: (hP b); srw if_pos // fsubst_σ // }
    scase: [∃ x ∈ s \ s', σ x = a]=> [/== ?|/==]
    { srw fsubst_out // fsubst_inE //== => y
      scase: [y ∈ s']=> // }
    move=> y ?? <-; srw fsubst_σ //
    move: (hP y)=> // }
  move=> hP; exists h ∘ σ=> ⟨!a|⟨|⟩⟩ //
  { scase: [a ∈ ssubst σ s s]
    { move=> aout; srw fsubst_out //
      shave aout : a ∉ ssubst σ s s'
      { move: aout; srw ?fsubst_inE // }
      scase: (bighstarDef_split _ _ hP)=> _ /(_ (bout)) -> // }
    sby move=>/fsubst_comp_σ  }
  move=> b; move: (hP $ σ b)
  scase: [b ∈ s']=> bin /==
  { srw if_neg // fsubst_inE // }
  srw fsubst_inE // Set.inter_eq_self_of_subset_right //
  srw if_pos //

open Classical

lemma fsubst_local_out (s') (h : hheap α) :
  hlocal s' h ->
  validSubst σ s s' ->
  validSubst σ s h ->
  x ∉ ssubst σ s s' ->
  fsubst σ s h x = ∅  := by
  move=> hl ?? xin
  by_cases H : (x ∈ ssubst σ s s)
  { move: H; srw fsubst_inE /== => x /[swap] ?
    subst_vars=> xin'; srw fsubst_σ; apply hl
    move: xin; srw fsubst_inE /== => // /(_ xin') /[swap] // }
  srw fsubst_out //


lemma validSubst_union :
  Disjoint s₁ s₂ ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  validSubst σ (s₁ ∪ s₂) s₁ := by
  move=> /Set.disjoint_left dj ?? /== /[swap]? [] ain [] //
  { move=> ? /(@Eq.symm _ _ _) // }
  move=> /dj; move: ain=> /dj //

lemma validSubst_union_l (h₁ h₂ : hheap α)
  (dj : Disjoint s₁ s₂)
  (σP : ∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) :
  (hlocal s₁ h₁) ->
  (hlocal s₂ h₂) ->
  validSubst σ (s₁ ∪ s₂) (h₁ ∪ h₂) ->
  validSubst σ (s₁ ∪ s₂) h₁ := by
  move=> hl₁ hl₂ vs a ain b bin /[dup] /σP ? /[dup]/(@Eq.symm _ _ _) /σP ?
  move=> /vs /(_ (ain)) /(_ (bin)) /==
  scase: ain bin
  { move=> /[dup]?/(Set.disjoint_left.mp dj) /hl₂->
    move=> /== [] // /(Set.disjoint_left.mp dj) /hl₂-> // }
  move=> /[dup]?/(Set.disjoint_left.mp dj) /hl₁->
  move=> /== [] // /(Set.disjoint_left.mp dj) /hl₁-> //

set_option maxHeartbeats 800000 in
lemma fsubst_union (h₁ h₂ : hheap α) :
  validSubst σ (s₁ ∪ s₂) h₁ ->
  validSubst σ (s₁ ∪ s₂) h₂ ->
  hlocal s₁ h₁ ->
  hlocal s₂ h₂ ->
  Disjoint s₁ s₂ ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  validSubst σ (s₁ ∪ s₂) (h₁ ∪ h₂) ->
  fsubst σ (s₁ ∪ s₂) h₁ ∪ fsubst σ (s₁ ∪ s₂) h₂ =
  fsubst σ (s₁ ∪ s₂) (h₁ ∪ h₂) := by
  move=> ?? hl₁ hl₂ dj σP vs !b /==
  shave ? : validSubst σ (s₁ ∪ s₂) s₁
  { apply validSubst_union=> // }
  shave ? : validSubst σ (s₁ ∪ s₂) s₂
  { srw Set.union_comm; apply validSubst_union=> //
    move=> ? /σP /[swap] ? /[apply] /[swap]->// }
  scase: [b ∈ ssubst σ (s₁ ∪ s₂) s₁]=> [bin'|]
  { srw (fsubst_local_out _ _ s₁) //==
    scase: [b ∈ ssubst σ (s₁ ∪ s₂) s₂]=> [bin|]
    { srw (fsubst_local_out _ _ s₂) //==
      srw (fsubst_local_out _ _ (s₁ ∪ s₂))=> //
      { move=> ? /== /hl₁-> /hl₂-> // }
      move: bin bin'; srw ?fsubst_inE //== => h₁ h₂
      move=> ? [] // }
    srw fsubst_inE // => /== a _ ain <-
    srw ?fsubst_σ //=
    shave->//: h₁ a = ∅; apply hl₁=> // }
  srw fsubst_inE // => /== a _ ain <-
  srw ?fsubst_σ //=

lemma validSubst_local:
  Set.InjOn σ s' ->
  s' ⊆ s ->
  hlocal s' h₁ ->
  (∀ᵉ (a ∈ s') (b ∉ s'), σ a ≠ σ b) ->
  validSubst σ s h₁ := by
  move=> inj ? hl σP a ? b ?
  scase: [a ∈ s']
  { scase: [b ∈ s']
    { move=> /hl->/hl// }
    move=> /σP/[apply]// }
  scase: [b ∈ s']
  {  move=> /σP/[apply]// }
  move=> /inj/[apply] //

set_option maxHeartbeats 800000 in
lemma fsubst_union_same (h₁ h₂ : hheap α) :
  Set.InjOn σ s' ->
  s' ⊆ s ->
  hlocal s' h₁ ->
  hlocal s' h₂ ->
  (∀ᵉ (a ∈ s') (b ∉ s'), σ a ≠ σ b) ->
  fsubst σ s h₁ ∪ fsubst σ s h₂ =
  fsubst σ s (h₁ ∪ h₂) := by
  move=> inj ? l₁ l₂ σP !b /==
  scase: [∃ a ∈ s', σ a = b]=> /==
  { move=> /== ?; srw ?fsubst partialInvSet
    scase: [∃ a ∈ s, σ a = b]=> /==
    { move=> ?; srw ?dif_neg // }
    move=> y [??]; srw ?dif_pos // }
  move=> a ? <-; srw ?fsubst_σ //
  all_goals apply validSubst_local=> //
  move=> ? /[dup] /l₁ /== -> /l₂ //

set_option maxHeartbeats 800000 in
lemma hsubst_hhstar (s₁ s₂ s) :
  s = s₁ ∪ s₂ ->
  Disjoint s₁ s₂ ->
  hhlocal s₁ H₁ ->
  hhlocal s₂ H₂ ->
  (∀ᵉ (a ∈ s₁) (b ∈ s₂), σ a ≠ σ b) ->
  hsubst σ s H₁ ∗ hsubst σ s H₂ = hsubst σ s (H₁ ∗ H₂) := by
  move=> ->  dj hl₁ hl₂ σP !hh !⟨|⟩
  { scase! => h₁ h₂ ![h₁ -> Hh₁ vs₁] ![h₂ -> Hh₂ vs₂] -> hdj
    shave ? : validSubst σ (s₁ ∪ s₂) (h₁ ∪ h₂)
    { move=> /== ???? /[dup]/vs₁-> // /vs₂ -> // }
    exists h₁ ∪ h₂; sdo 2 constructor
    { apply fsubst_union=> // }
    { exists h₁, h₂; sdo 3 constructor=> //
      move=> a
      scase: [a ∈ (s₁ ∪ s₂)]=> [|/==?]/==
      { move=> /hl₁/(_ Hh₁)-> /hl₂/(_ Hh₂)-> // }
      move: (hdj (σ a)); srw ?fsubst_σ //== }
    sdone }
  scase! => hh -> ![h₁ h₂ Hh₁ Hh₂ -> hdj vs]
  shave ? : validSubst σ (s₁ ∪ s₂) h₁
  { apply validSubst_union_l=> // }
  shave ? : validSubst σ (s₁ ∪ s₂) h₂
  { srw Set.union_comm; apply validSubst_union_l=> //
    { move=> * /(@Eq.symm _ _ _) // }
    srw Set.union_comm hunion_comm_of_hdisjoint //
    apply hdisjoint_symm=> // }
  exists fsubst σ (s₁ ∪ s₂) h₁
  exists fsubst σ (s₁ ∪ s₂) h₂=> ⟨|⟨|⟨|⟩⟩⟩
  { exists h₁ }
  { exists h₂ }
  { srw fsubst_union=> // }
  move=> a
  scase: [a ∈ ssubst σ (s₁ ∪ s₂) (s₁ ∪ s₂)]=> [?|]
  { srw ?fsubst_out // }
  srw fsubst_inE /== => ? /[swap] <- xin
  srw ?fsubst_σ //

set_option maxHeartbeats 800000 in
lemma hsubst_hhstar_same (s' s) :
  s' ⊆ s ->
  hhlocal s' H₁ ->
  hhlocal s' H₂ ->
  Set.InjOn σ s' ->
  (∀ᵉ (a ∈ s') (b ∉ s'), σ a ≠ σ b) ->
  hsubst σ s H₁ ∗ hsubst σ s H₂ = hsubst σ s (H₁ ∗ H₂) := by
  move=> ? l₁ l₂ σP inj !h ! ⟨![?? ![h₁ -> Hh₁ vs₁] ![h₂ -> Hh₂ vs₂] -> dj]|⟩
  { exists (h₁ ∪ h₂)=> ⟨|⟨|⟩⟩
    { srw (fsubst_union_same σ s) // }
    { exists h₁, h₂=> ⟨//|⟨//|⟨//|a⟩⟩⟩
      scase: [a ∈ s]=> ?
      { srw (l₁ _ Hh₁ _) ?(l₂ _ Hh₂ _) // }
      move: (dj (σ a)); srw ?fsubst_σ  // }
    apply validSubst_local=> //
    move=> ? /[dup] /(l₁ _ Hh₁) /== -> /l₂ // }
  scase! => h -> ![h₁ h₂] ?? -> ? ?
  exists (fsubst σ s h₁), (fsubst σ s h₂)=> ⟨|⟨|⟨|⟩⟩⟩
  { exists h₁=> ⟨//|⟨//|⟩⟩; apply validSubst_local=> // }
  { exists h₂=> ⟨//|⟨//|⟩⟩; apply validSubst_local=> // }
  { srw (fsubst_union_same σ s) // }
  move=> b
  scase: [∃ a ∈ s', σ a = b]=> /==
  { move=> /== ?; srw ?fsubst partialInvSet
    scase: [∃ a ∈ s, σ a = b]=> /==
    { move=> ?; srw ?dif_neg // }
    move=> y [??]; srw ?dif_pos // }
  move=> a ? <-; srw ?fsubst_σ //
  all_goals apply validSubst_local=> //

@[simp]
lemma fsubst0 : fsubst σ s (∅ : hheap α) = ∅ := by
  move=> ! x
  srw fsubst; scase: (partialInvSet s σ x)=> //


@[simp]
lemma hsubst0 : hsubst σ s emp = emp := by
  move=> !h !⟨![h -> -> ?] |->⟩ //
  exists ∅=> ⟨//|⟨//| ? //⟩⟩

@[simp]
lemma hhlocal_sum (H : γ -> _) :
  hhlocal s' (∑ x ∈ fs, H x) = (∀ x ∈ fs, hhlocal s' (H x)) := by
  induction fs using Finset.induction=> /==
  { move=> ? // }
  srw Finset.sum_insert ?hhProp_add_def //

set_option maxHeartbeats 800000 in
lemma hsubst_hhstar_sum_same (fs : Finset γ) (H : γ -> _) (s' s) :
  s' ⊆ s ->
  (∀ i ∈ fs, hhlocal s' (H i)) ->
  Set.InjOn σ s' ->
  (∀ᵉ (a ∈ s') (b ∉ s'), σ a ≠ σ b) ->
  hsubst σ s (Finset.sum fs H) = ∑ i in fs, hsubst σ s (H i) := by
  move=> ? /[swap] ?
  induction fs using Finset.induction=> /==
  rename_i b fs _ ih=> ???
  srw ?Finset.sum_insert //' ?hhProp_add_def
  srw -(hsubst_hhstar_same σ s') //' //


lemma hsubst_hhexists :
  hsubst σ s (hhexists H) = hhexists (fun x => hsubst σ s (H x)) := by
  move=> !h !⟨![h -> [?] ?? ⟨//|/= ⟨|⟩ //⟩]| [?] /= ![?->??]⟨|⟩ //⟩

lemma hsubst_hwp (Q : hval α -> hhProp α) (σ : α -> β) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  (hhlocal s H) ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  H ==> hwp s (ht ∘ σ) Q ->
  hsubst σ s H ==> hwp (ssubst σ s s) ht fun hv => hsubst σ s (Q (hv ∘ σ)) := by
  sby move=> ? Hl ?? ? ![h -> ??]; apply hsubst_heval

lemma hwp_hsubst (Q : hval α -> hhProp α) (σ : α -> β) :
  hhlocal s H ->
  (∀ hv, hhlocal s (Q hv)) ->
  Set.InjOn σ s ->
  (hsubst σ s H ==> hwp (ssubst σ s s) ht fun hv => hsubst σ s (Q (hv ∘ σ))) ->
  H ==> hwp s (ht ∘ σ) Q := by
  move=> hl ql inj wp h /[dup] /hl {}hl Hh; apply heval_hsubst=> //
  { sby move=> > /ql hl' ? /[dup] /hl -> }
  sby apply wp; exists h=> ⟨//|⟨//|⟩⟩; apply injectiveSet_validSubst

lemma hsubst_wp1 (Q' : hval β -> hhProp α) (Q : hval α -> hhProp α) (σ : α -> β) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  (hhlocal s H) ->
  (s = s₁ ∪ s₂) ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  (∀ hv, Q' hv = Q (hv ∘ σ)) ->
  LGTM.triple
    [⟨s₁, ht₁ ∘ σ⟩]
    H
    Q ->
  LGTM.triple
    [⟨ssubst σ s s₁, ht₁⟩]
    (hsubst σ s H)
    fun hv => hsubst σ s (Q' hv) := by sorry

lemma hsubst_wp (Q' : hval β -> hhProp α) (Q : hval α -> hhProp α) (σ : α -> β) :
  (∀ᵉ (a ∈ s) (a' ∉ s), σ a ≠ σ a') ->
  (hhlocal s H) ->
  (s = s₁ ∪ s₂) ->
  (∀ hv₁ hv₂, Set.EqOn hv₁ hv₂ s -> Q hv₁ = Q hv₂) ->
  (∀ hv, Q' hv = Q (hv ∘ σ)) ->
  LGTM.triple
    [⟨s₁, ht₁ ∘ σ⟩, ⟨s₂, ht₂ ∘ σ⟩]
    H
    Q ->
  LGTM.triple
    [⟨ssubst σ s s₁, ht₁⟩, ⟨ssubst σ s s₂, ht₂⟩]
    (hsubst σ s H)
    fun hv => hsubst σ s (Q' hv) := by sorry

lemma wp_hsubst_some [Inhabited α] (Q : hval α -> hhProp α) :
  s = s₁ ∪ s₂ ->
  hhlocal s H ->
  (∀ hv, hhlocal s (Q hv)) ->
  LGTM.triple
    [⟨ssubst some s s₁, ht₁ ∘ Option.get!⟩, ⟨ssubst some s s₂, ht₂ ∘ Option.get!⟩]
    (hsubst some s H)
    (fun hv => hsubst some s (Q (hv ∘ some))) ->
  LGTM.triple
    [⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩]
    H
    Q := by sorry

attribute [simp] Option.any

@[simp]
lemma ssubst_some_inE [Inhabited α] (s s' : Set α) (x : Option α) :
  x ∈ ssubst some s s' ↔ (∃ y ∈ x, (y ∈ s ∩ s')) := by
  srw fsubst_inE => [⟨|⟩|?//] /==
  { move=> ??? <- /== // }
  sby scase: x

lemma hsubst_some_hhstar (s₁ s₂) [Inhabited α] (H₂ : α -> hProp) :
  hhlocal s₁ H₁ ->
  Disjoint s₁ s₂ ->
  s = s₁ ∪ s₂ ->
  hsubst some s (H₁ ∗ bighstar s₂ H₂) =
  hsubst some s H₁∗ [∗ i in ssubst some s s₂| H₂ i.get!] := by
  move=> ? /[dup] /Set.disjoint_left ?? ->
  srw -(hsubst_hhstar (s₁ := s₁) (s₂ := s₂)) //'; rotate_left
  { move=> ?? ?? [] // }
  srw (bighstar_eq (H' := (H₂ ∘ Option.get!) ∘ some)) //
  generalize heq: (H₁ ∘ Option.get!) = H'
  generalize req: (H₂ ∘ Option.get!) = R'=> /=
  srw ?hsubst_bighstar //'; rotate_left
  -- { move=> * [] // }
  { move=> // }
  { move=> * [] // }
  -- { move=> // }
  -- subst_vars=> /== //

lemma hsubst_some_hhstar' (s₁ s₂) [Inhabited α] (H₁ H₂ : hhProp α) :
  hhlocal s₁ H₁ ->
  hhlocal s₁ H₂ ->
  Disjoint s₁ s₂ ->
  s = s₁ ∪ s₂ ->
  hsubst some s (H₁ ∗ H₂ ∗ bighstar s₂ H₃) =
  hsubst some s H₁ ∗
  hsubst some s H₂ ∗
  [∗ i in ssubst some s s₂| H₃ i.get!] := by
  move=> *; srw -?hhstar_assoc (hsubst_some_hhstar _ s₁ s₂) //'
  srw (hsubst_hhstar_same _ s₁ ) // => ? // * [] //

lemma ssubst_some_union [Inhabited α] (s s₁ s₂ : Set α) :
  ssubst some s (s₁ ∪ s₂) =
  ssubst some s s₁ ∪ ssubst some s s₂ := by
  move=> ! [] /== v ⟨|⟩ // [] //

lemma ssubst_some_disjoint [Inhabited α] :
  Disjoint s₁ s₂ ->
  Disjoint (ssubst some s s₁) (ssubst some s s₂) := by
  move=> /Set.disjoint_left dj
  srw Set.disjoint_left=> /== ?? -> //

lemma hhlocal_some :
  s' ⊆ s ->
  hhlocal s' H₀ ->
  hhlocal (ssubst some s s') (hsubst some s H₀) := by
  move=> ? l ? ![h -> ? _] ??
  apply fsubst_local_out=> //'
  move=> ? //

lemma hhlocal_subset (s'') :
  s'' ⊆ s' ->
  hhlocal s'' H -> hhlocal s' H := by
  move=> ss hl ? /hl /[swap] a /(_ a) /[swap]? -> //

lemma fsubst_subset_set_local :
  s' ⊆ s ->
  hlocal s' H ->
  fsubst some s' H = fsubst some s H := by
  move=> ? l !
  shave ?: hlocal s H
  { apply hhlocal_subset s'=> //' }
  shave ?: validSubst some s H
  { move=> ? // }
  shave ?: validSubst some s' H
  { move=> ? // }
  shave ?:  ∀ (s s' : Set α), validSubst some s' s
  { move=> ??? // }
  shave ?: ∀ (s s' : Set α), none ∉ ssubst some s s'
  { move=> ??; srw fsubst_inE // }
  shave ?: none ∉ ssubst some s' s
  { srw fsubst_inE // }
  scase
  { srw ?fsubst_local_out // }
  move=> a
  scase: [a ∈ s]
  { move=> ?; srw ?fsubst_local_out // fsubst_inE //  }
  move=> ?; srw [2]fsubst_σ //
  scase: [a ∈ s']
  { move=> /[dup] /l-> ?; srw ?fsubst_local_out // fsubst_inE // }
  move=> ?; srw fsubst_σ //



end hsubst
