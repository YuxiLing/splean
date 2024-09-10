import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.HProp


open Classical

section HHProp

variable {α : Type} [DecidableEq α]

abbrev hheap (α : Type) := α -> heap
abbrev hhProp (α : Type) := @hheap α -> Prop

def hunion (h₁ h₂ : @hheap α) : @hheap α :=
  λ a => h₁ a ∪ h₂ a

@[simp]
noncomputable def hHeap.add [PartialCommMonoid val] (h₁ h₂ : @hheap α) : @hheap α :=
  λ a => h₁ a +ʰ h₂ a

infixr:55 (priority := high) " +ʰ " => hHeap.add

instance (α : Type) : Union (@hheap α) := ⟨hunion⟩

@[simp]
def hdisjoint (h₁ h₂ : @hheap α) : Prop :=
  ∀ a, Finmap.Disjoint (h₁ a) (h₂ a)

@[simp]
def hValidInter [PartialCommMonoid val] (h₁ h₂ : @hheap α) : Prop :=
  ∀ a, (h₁ a) ⊥ʰ (h₂ a)

infixr:55 " ⊥ʰ " => hValidInter

def hhstar (hH₁ hH₂ : @hhProp α) : (@hhProp α) :=
  fun (hh : @hheap α) =>
    exists (hh₁ hh₂ : @hheap α),
      hH₁ hh₁ ∧ hH₂ hh₂ ∧ hh = hh₁ ∪ hh₂ ∧ hdisjoint hh₁ hh₂

@[default_instance]
instance (α : Type) : HStar (@hhProp α) (@hhProp α) (@hhProp α) := ⟨hhstar⟩

local notation "hhProp" => @hhProp α
local notation "hheap" => @hheap α

@[simp]
def hEmpty : hheap := fun _ => ∅

instance : EmptyCollection hheap := ⟨hEmpty⟩

@[simp]
def hEmptyE : (∅ : hheap) a = ∅ := by rfl

def hSingle (a : α) (p : loc) (v : val) : hheap :=
  λ a' => if a = a' then Finmap.singleton p v else ∅

-- def bighstar (s : Set α) [DecidablePred (· ∈ s)]  (h : heap) : hheap :=
--   λ a => if a ∈ s then h else ∅

@[simp]
lemma unionE {h₁ h₂ : hheap} {a : α} : (h₁ ∪ h₂) a = h₁ a ∪ h₂ a := by rfl

abbrev hhimpl (H₁ H₂ : hhProp) : Prop :=
  forall h, H₁ h -> H₂ h

infixr:51 (priority := high) " ==> " => hhimpl

def hqimpl {A} (Q₁ Q₂ : A → hhProp) : Prop :=
  forall (v:A), Q₁ v ==> Q₂ v

infixr:51 (priority := high) " ===> " => hqimpl

-- variable (hH₁ hH₂ : hhProp)

noncomputable def extend (s : Set α) (h : α -> heap) : hheap :=
  fun a => if a ∈ s then h a else ∅

@[simp]
def bighstarDef (s : Set α) (hH : α -> hProp) (h₀ : hheap) : hhProp :=
  fun h => ∀ a, if a ∈ s then hH a (h a) else h a = h₀ a


def bighstar (s : Set α) (hH : α -> hProp) : hhProp :=
  bighstarDef s hH hEmpty

notation "[∗" i " in " s "| " h "]" => bighstar s (fun i => h)
notation "[∗ in " s "| " h "]" => bighstar s (fun _ => h)

def hhempty : hhProp := (· = ∅)

notation:max (priority := high) "emp" => hhempty

abbrev hhsingle (s : Set α) (p : α -> loc) (v : α -> val) : hhProp := [∗ i in s | p i ~~> v i]

-- notation:60 p:57 " ~" s:max "~> " v:57 => hhsingle s p v
-- notation:60 p:57 " ~" s:max "~> " v:57 => hhsingle s (fun _ => p) (fun _ => v)
-- notation:60 p:57 " ~" s:max "~> " v:57 => hhsingle s p (fun _ => v)
-- notation:60 p:57 "(" s ")|-> " v:57 => hhsingle s (fun _ => p) (fun _ => v)
notation:60 p:57 "~⟨" i " in " s "⟩~> " v:57 => hhsingle s (fun i => p) (fun i => v)
notation:60 p:57 "~" s:max "~> " v:57 => hhsingle s (fun i => p) (fun i => v)


def hhexists {A} (P : A → hhProp) : hhProp :=
  fun hh => exists (v:A), P v hh

def hhforall {A} (P : A → hhProp) : hhProp :=
  fun hh => forall (v:A), P v hh

section
open Lean.TSyntax.Compat
macro (priority := high) "∃ʰ" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hhexists xs b
macro (priority := high) "h∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hhforall xs b
end

@[app_unexpander hhexists] def unexpandHHExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ʰ $xs:binderIdent*, $b) => `(∃ʰ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∃ʰ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃ʰ ($x:ident : $t), $b)
  | t                                              => pure t

@[app_unexpander hhforall] def unexpandHHForall : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∀ $xs:binderIdent*, $b) => `(h∀ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∀ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∀ ($x:ident : $t), $b)
  | t                                              => pure t


def hhpure (P : Prop) : hhProp :=
  hhexists (fun (_ : P) => emp)

def hhtop : hhProp :=
  hhexists (fun (h : hhProp) => h)

def hhwand (h1 h2 : hhProp) : hhProp :=
  hhexists (fun (h0 : hhProp) => h0 ∗ (hhpure (h1 ∗ h0 ==> h2)))

@[default_instance]
instance : HWand hhProp hhProp hhProp := ⟨hhwand⟩

def hqwand {A} (q1 q2 : A → hhProp) : hhProp :=
  hhforall (fun (x : A) => (q1 x) -∗ (q2 x))

notation:max (priority := high) "⌜" P "⌝" => hhpure P

/- ⊤⊤ is very annoynig, let's just overwrite lean's ⊤ -/
notation (priority := high) "⊤" => hhtop

def hqstar {A} (q : A → hhProp) (h : hhProp) : A → hhProp :=
  fun x => (q x) ∗ h


instance (A : Type) : HStar (A → hhProp) hhProp (A → hhProp) where
  hStar := hqstar

lemma hqstarE {A} (q : A → hhProp) (h : hhProp) (a : A) : (q ∗ h) a = q a ∗ h := by rfl

instance (α : Type) : HWand (α → hhProp) (α → hhProp) hhProp where
  hWand := hqwand

/- =================== Useful Properties of Hyper Heaps =================== -/

lemma hunion_empty (h₁ : hheap) :
  h₁ ∪ ∅ = h₁ := by
  funext=> /=
  apply Finmap.union_empty

@[simp]
lemma hHeap.add_empty_r [PartialCommMonoid val] (h : hheap) :
  h +ʰ ∅ = h := by
  funext=> /==

lemma empty_hunion (h : hheap) :
  ∅ ∪ h = h := by
  funext=> /=
  apply Finmap.empty_union

@[simp]
lemma hHeap.add_empty_l [PartialCommMonoid val] (h : hheap) :
  ∅ +ʰ h = h := by
  funext=> /==

lemma hunion_comm_of_hdisjoint (h₁ h₂ : hheap) :
  hdisjoint h₁ h₂ → h₁ ∪ h₂ = h₂ ∪ h₁ := by
  move=> /= ?
  apply funext=> > /=
  sby apply Finmap.union_comm_of_disjoint

lemma hHeap.add_comm [PartialCommMonoid val] (h₁ h₂ : hheap) :
  h₁ +ʰ h₂ = h₂ +ʰ h₁ := by
  move=> ! /== ?; apply Heap.add_comm


lemma hunion_assoc (h₁ h₂ h₃ : hheap) :
  h₁ ∪ h₂ ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  funext=> /=
  apply Finmap.union_assoc

lemma hHeap.add_assoc [PartialCommMonoid val] (h₁ h₂ h₃ : hheap) :
  (h₁ +ʰ h₂) +ʰ h₃ = h₁ +ʰ (h₂ +ʰ h₃) := by
  funext=> /=; srw Heap.add_assoc


lemma hdisjoint_symm (h₁ h₂ : hheap ) :
  hdisjoint h₁ h₂ → hdisjoint h₂ h₁ := by
  move=> /= ? >
  sby apply Finmap.Disjoint.symm

lemma hValidInter_symm [PartialCommMonoid val] (h₁ h₂ : hheap ) :
  h₁ ⊥ʰ h₂ → h₂ ⊥ʰ h₁ := by
  move=> /= ? >
  sby srw validInter_comm


lemma hdisjoint_hunion_left (h₁ h₂ h₃ : hheap) :
  hdisjoint (h₁ ∪ h₂) h₃ ↔ hdisjoint h₁ h₃ ∧ hdisjoint h₂ h₃ := by
  move=> /=
  sby srw Finmap.disjoint_union_left

@[simp]
lemma hValidInter_add_left [PartialCommMonoid val] (h₁ h₂ h₃ : hheap) :
  hValidInter (h₁ +ʰ h₂) h₃ ↔ hValidInter h₁ h₃ ∧ hValidInter h₂ h₃ := by
  sdone


lemma hdisjoint_hunion_right (h₁ h₂ h₃ : hheap) :
  hdisjoint h₁ (h₂ ∪ h₃) ↔ hdisjoint h₁ h₂ ∧ hdisjoint h₁ h₃ := by
    move=> /=
    sby srw Finmap.disjoint_union_right

@[simp]
lemma hValidInter_add_right [PartialCommMonoid val] (h₁ h₂ h₃ : hheap) :
  hValidInter h₁ (h₂ +ʰ h₃) ↔ hValidInter h₁ h₂ ∧ hValidInter h₁ h₃ := by
  sdone


/- ============ Properties of Hyper Separation Logic Operators ============ -/

/- ------------------ Properties of [hhimpl] and [hqimpl] ----------------- -/

lemma hhimpl_refl (h : hhProp) : h ==> h :=
  fun _ => id

lemma hhimpl_trans {h₁ h₂ h₃ : hhProp} : h₁ ==> h₂ -> h₂ ==> h₃ -> h₁ ==> h₃ :=
  fun h₁h₂ h₂h₃ hh HH₁ => h₂h₃ hh (h₁h₂ hh HH₁)

lemma hhimpl_trans_r  (h₁ h₂ h₃ : hhProp) : h₂ ==> h₃ -> h₁ ==> h₂ -> h₁ ==> h₃ :=
  fun h₂h₃ h₁h₂ hh HH₁ => h₂h₃ hh (h₁h₂ hh HH₁)

lemma hhimpl_antisymm {h₁ h₂ : hhProp} : h₁ ==> h₂ -> h₂ ==> h₁ -> h₁ = h₂ :=
  fun h₁h₂ h₂h₁ => funext (fun hh => propext ⟨h₁h₂ hh, h₂h₁ hh⟩)

lemma hhprop_op_comm (op : hhProp -> hhProp -> hhProp) (h1 h2 : hhProp) :
  (∀ h1 h2, op h1 h2 ==> op h2 h1) -> op h1 h2 = op h2 h1 :=
  fun hcomm => hhimpl_antisymm (hcomm h1 h2) (hcomm h2 h1)

/- ---------------- Properties of [hhempty] ---------------- -/

lemma hhempty_intro : emp (∅ : hheap) :=
  by simp [hhempty, hEmpty]

lemma hhempty_inv {h : hheap} : emp h -> h = ∅ :=
  by simp [hhempty, hEmpty]

@[simp]
lemma bighstarDef0 (h : α -> _) : bighstarDef ∅ h h₀ = (· = h₀) :=
  by sby unfold bighstarDef=> !? /== ⟨?!|->⟩

@[simp]
lemma bighstar0 (h : α -> _) : [∗ i in ∅ | h i] = (emp : hhProp) :=
  by sby srw bighstar bighstarDef0

lemma bighstar_hhempty (s : Set α) [DecidablePred (· ∈ s)] :
   [∗ in s | hempty] = emp :=
  by sby unfold hhempty bighstar bighstarDef hEmpty=> /= !?; simp[hempty]=> ⟨?!|->⟩



/- ---------------- Properties of [hstar] ---------------- -/

lemma hhstar_intro : ∀ {hH₁ hH₂ : hhProp} {h₁ h₂ : hheap}, hH₁ h₁ -> hH₂ h₂ ->
  hdisjoint h₁ h₂ -> (hH₁ ∗ hH₂) (h₁ ∪ h₂) :=
  by sdone

lemma hhstar_inv {hH₁ hH₂ : hhProp} {h : hheap} : (hH₁ ∗ hH₂) h ->
  exists (h₁ h₂ : hheap), hH₁ h₁ ∧ hH₂ h₂ ∧ h = h₁ ∪ h₂ ∧ hdisjoint h₁ h₂ :=
  by sapply

lemma hhstar_comm {hH₁ hH₂ : hhProp} : hH₁ ∗ hH₂ = hH₂ ∗ hH₁ := by
  apply hhprop_op_comm=> > ? ![>??] ->
  move=> /hdisjoint_symm /[dup] ? /hunion_comm_of_hdisjoint ?
  sby exists w_1, w

lemma hhstar_assoc {hH₁ hH₂ hH₃ : hhProp} : (hH₁ ∗ hH₂) ∗ hH₃ = hH₁ ∗ (hH₂ ∗ hH₃) := by
  apply hhimpl_antisymm=> ?
  { move=> ![] > ![] > ?? -> ?? -> /hdisjoint_hunion_left [] *
    exists w_2, w_3 ∪ w_1
    sdo 3 apply And.intro=> //
    apply hunion_assoc
    sby srw hdisjoint_hunion_right }
  { move=> ![] > ? ![] > ?? -> ? -> /hdisjoint_hunion_right [] *
    exists w ∪ w_2, w_3
    sdo 3 apply And.intro=> //
    srw ?hunion_assoc
    sby srw hdisjoint_hunion_left }

lemma hhstar_hhempty_l {hH : hhProp} : emp ∗ hH = hH := by
  apply hhimpl_antisymm=> h
  { move=> ![] > /hhempty_inv -> ? ->
    sby srw empty_hunion }
  move=> ?
  exists ∅, h
  srw empty_hunion => /=
  repeat (constructor=> //)=> >
  apply Finmap.disjoint_empty

lemma hhstar_hhempty_r {hH : hhProp} : hH ∗ emp = hH := by
  srw hhstar_comm
  apply hhstar_hhempty_l

lemma hhstar_hhexists_l {A} {P : A → hhProp} {hH : hhProp} :
  (hhexists P) ∗ hH = hhexists (fun x => P x ∗ hH) := by
  apply hhimpl_antisymm
  { sby move=> > ![] > [] }
  sby move=> > ![]

lemma hhstar_hhforall_l {A} {_ : Nonempty A} {P : A → hhProp} {hH : hhProp} :
  (hhforall P) ∗ hH ==> hhforall (fun x => P x ∗ hH) := by
  move=> ? ![] > /hhforall * ?
  sby exists w, w_1

lemma choose_fun {α β : Type} (b₀ : β)  (p : α -> β -> Prop) (s : Set α) :
  (∀ a ∈ s, ∃ b : β, p a b) -> (∃ f : α -> β, (∀ a ∈ s, p a (f a))) := by
  move=> pH
  exists (fun a => if h : a ∈ s then choose (pH a h) else b₀)=> /=
  move=> a inS
  srw dif_pos //; apply choose_spec

-- lemma hhstar_hhforall_inc {A : Type} {_ : Nonempty A} {P : A → hhProp} {hH : hhProp} :
--   hhforall (fun x => P x ∗ hH) ==> (hhforall P) ∗ hH := by
--   move=> h /hhforall /HStar.hStar/instHStarHhProp/=
--   unfold hhstar
--   move=> /skolem[h₁]/skolem[h₂] hH


lemma hhimpl_frame_l (hH₁ hH₂ hH₃ : hhProp) :
  hH₁ ==> hH₂ -> hH₁ ∗ hH₃ ==> hH₂ ∗ hH₃ := by
  srw hhimpl=> ?? ![] > *
  sby exists w, w_1

lemma hhimpl_frame_r (hH₁ hH₂ hH₃ : hhProp) :
  hH₁ ==> hH₂ -> hH₃ ∗ hH₁ ==> hH₃ ∗ hH₂ := by
  srw hhimpl=> ?? ![] > *
  sby exists w, w_1

lemma hhimpl_frame_lr (hH₁ hH₂ hH₃ hH₄ : hhProp) :
  hH₁ ==> hH₂ -> hH₃ ==> hH₄ -> hH₁ ∗ hH₃ ==> hH₂ ∗ hH₄ := by
  srw !hhimpl=> ?? > ![] > *
  sby exists w, w_1

lemma hhimpl_hhstar_trans_l {hH1 hH2 hH3 hH4 : hhProp} :
  hH1 ==> hH2 →
  hH2 ∗ hH3 ==> hH4 →
  hH1 ∗ hH3 ==> hH4 :=
by
  srw !hhimpl => ? hStar23 ? ![h1 h3 *]
  apply hStar23
  sby exists h1, h3

lemma hhimpl_hhstar_trans_r {hH1 hH2 hH3 hH4 : hhProp} :
  hH1 ==> hH2 →
  hH3 ∗ hH2 ==> hH4 →
  hH3 ∗ hH1 ==> hH4 :=
by
  srw !hhimpl => ? hStar32 ? ![h3 h1 *]
  apply hStar32
  sby exists h3, h1

/- --------------- Properties of [hhpure] --------------- -/

lemma hhpure_intro (P : Prop) :
  P → (⌜P⌝ : hhProp) ∅ :=
by sdone

lemma hhpure_inv (P : Prop) (h : hheap) :
  ⌜P⌝ h →
  P ∧ h = ∅ :=
by
  sby move=> []

lemma hhstar_hhpure_l (P : Prop) (H : hhProp) (h : hheap) :
  ((⌜P⌝ : hhProp) ∗ H) h = (P ∧ H h) :=
by
  srw hhpure hhstar_hhexists_l hhstar_hhempty_l
  sby move=> ! ⟨|⟩ []

lemma hhstar_hhpure_r (P : Prop) (H : hhProp) (h : hheap) :
  (H ∗ (⌜P⌝ : hhProp)) h = (H h ∧ P) :=
by
  sby srw hhstar_comm hhstar_hhpure_l

lemma hhimpl_hhstar_hhpure_r (P : Prop) (H H' : hhProp) :
   P →
   (H ==> H') →
   H ==> ⌜P⌝ ∗ H' :=
by
  srw !hhimpl => *
  sby srw hhstar_hhpure_l

lemma hhpure_inv_hhempty (P : Prop) (h : hheap) :
  ⌜P⌝ h →
  P ∧ emp h :=
by
  sby srw -hhstar_hhpure_l hhstar_hhempty_r

lemma hhpure_intro_hhempty (P : Prop) (h : hheap) :
  emp h → P → ⌜P⌝ h :=
by
  sby move=> *

lemma hhimpl_hempty_hhpure (P : Prop) :
  P → (emp : hhProp) ==> ⌜P⌝ :=
by
  sby move=> ???

lemma hhimpl_hstar_hhpure_l (P : Prop) (H H' : hhProp) :
  (P → H ==> H') →
  (⌜P⌝ ∗ H) ==> H' :=
by
  srw hhimpl=> * ?
  sby srw hhstar_hhpure_l

lemma hempty_eq_hhpure_true :
  (emp : hhProp) = ⌜True⌝ :=
by
  apply hhimpl_antisymm
  { move=> * ; sby apply hhpure_intro_hhempty }
  sby move=> ? []

lemma hhfalse_hhstar_any (H : hhProp) :
  ⌜False⌝ ∗ H = ⌜False⌝ :=
by
  apply hhimpl_antisymm
  { move=> ? ; sby srw hhstar_hhpure_l }
  move=> ? []
  sby srw hhstar_hhpure_l

/- ----------------- Properties of [hhexists] ----------------- -/

lemma hhexists_intro {A : Type} (x : A) (J : A → hhProp) (h : hheap) :
  J x h → (hhexists J) h :=
by sdone

lemma hhexists_inv {A : Type} (J : A → hhProp) (h : hheap) :
  (hhexists J) h → exists (x : A), J x h :=
by
  sby srw hhexists

lemma hhimpl_hhexists_l.{u} {A : Sort u} {H : hhProp} (J : A → hhProp) :
  (forall (x : A), J x ==> H) → (hhexists J) ==> H :=
by
  srw [0](hhimpl)=> hJx ? [?]
  sby apply hJx

lemma hhimpl_hhexists_r.{u} {A : Sort u} (x : A) {H : hhProp} (J : A → hhProp) :
  (H ==> J x) →
  H ==> (hhexists J) :=
by
  srw hhimpl=> * ??
  sby exists x

lemma hhimpl_hhexists {A : Type} (J1 J2 : A → hhProp) :
  J1 ===> J2 →
  hhexists J1 ==> hhexists J2 :=
by
  srw hqimpl=> hJs
  sby apply hhimpl_hhexists_l=> ?? /hJs

/- ------------------- Properties of [hhforall] ------------------- -/

lemma hhforall_intro {A : Type} (J : A → hhProp) (h : hheap) :
  (∀ x, J x h) → (hhforall J) h :=
by sdone

lemma hhforall_inv {A : Type} (J : A → hhProp) (h : hheap) :
  (hhforall J) h → ∀ x, J x h :=
by
  sby srw hhforall

lemma hhimpl_hhforall_r {A : Type} (J : A → hhProp) (H : hhProp) :
  (∀ x, H ==> J x) →
  H ==> (hhforall J) :=
by
  sby srw [0]hhimpl=> * ?

lemma hhimpl_hhforall_l {A : Type} (x : A) (J : A → hhProp) (H : hhProp) :
  (J x ==> H) →
  (hhforall J) ==> H :=
by
  srw hhimpl=> ??
  sby srw hhforall

lemma hhforall_specialize {A : Type} (x : A) (J : A → hhProp) :
  (hhforall J) ==> (J x) :=
by
  move=> ? ; sapply

lemma hhimpl_hhforall {A : Type} (J1 J2 : A → hhProp) :
  J1 ===> J2 →
  hhforall J1 ==> hhforall J2 :=
by
  srw hqimpl=> hQimp
  apply hhimpl_hhforall_r=> ?
  apply hhimpl_hhforall_l
  move: hQimp ; sapply

/- ----------------- Properties of [hqwand] ----------------- -/

lemma hhwandE :
  H1 -∗ H2 = hhexists (fun (H0 : hhProp) => H0 ∗ hhpure ((H1 ∗ H0) ==> H2)) := rfl

attribute [simp] hhwandE hqstarE

lemma hhwand_equiv (H0 H1 H2 : hhProp) :
  (H0 ==> H1 -∗ H2) ↔ (H1 ∗ H0 ==> H2) :=
by
  srw hhwandE ; apply Iff.intro
  { srw hhstar_comm=> ?
    apply hhimpl_hhstar_trans_l=>//
    srw hhstar_hhexists_l
    apply hhimpl_hhexists_l=> ?
    srw [2](hhstar_comm) (hhstar_assoc) [2](hhstar_comm)
    sby apply hhimpl_hstar_hhpure_l }
  move=> ?
  apply hhimpl_hhexists_r
  rw [<-(@hhstar_hhempty_r _ H0)]
  apply hhimpl_frame_r ; sby apply hhimpl_hempty_hhpure


lemma hqwand_equiv (Q2 Q1 : β -> hhProp) :
  H ==> (Q1 -∗ Q2) <-> (Q1 ∗ H) ===> Q2 := by
    constructor=> imp
    { move=> v /== h ![h₁ h₂] /[swap] /imp /(_ v)/=
      scase! => H' hh ? ? ![]/= imp ->->_ ? ->
      sby srw ?hunion_empty=> ?; apply imp }
    apply hhimpl_hhforall_r=> ?
    sby srw hhwand_equiv; apply imp

lemma hqwand_specialize A (x : A) (Q1 Q2 : A → hhProp) :
  (Q1 -∗ Q2) ==> (Q1 x -∗ Q2 x) :=
by
  sby apply (@hhimpl_hhforall_l α A x)=> ?; sapply

lemma hhimpl_hhwand_r (H1 H2 H3 : hhProp) :
  (H2 ∗ H1) ==> H3 →
  H1 ==> (H2 -∗ H3) :=
by
  sby srw hhwand_equiv

lemma hhimpl_hhwand_r_inv (H1 H2 H3 : hhProp) :
  H1 ==> (H2 -∗ H3) →
  (H2 ∗ H1) ==> H3 :=
by
  sby srw -hhwand_equiv

lemma hhwand_cancel (H1 H2 : hhProp) :
  (H1 ∗ (H1 -∗ H2)) ==> H2 :=
by
  sby apply hhimpl_hhwand_r_inv=> ?

lemma hhimpl_hempty_hhwand_same (H : hhProp) :
  emp ==> (H -∗ H) :=
by
  apply hhimpl_hhwand_r
  sby srw hhstar_hhempty_r=> h

lemma hhwand_hempty_l (H : hhProp) :
  (emp -∗ H) = H :=
by
  apply hhimpl_antisymm
  { rw [<- (@hhstar_hhempty_l _ (emp -∗ H))]
    apply hhwand_cancel }
  apply hhimpl_hhwand_r
  sby srw hhstar_hhempty_l=> ?

lemma hhwand_hhpure_l (P : Prop) (H : hhProp) :
  P → (⌜P⌝ -∗ H) = H :=
by
  move=> ? ; apply hhimpl_antisymm
  { apply hhimpl_trans
    apply (hhimpl_hhstar_hhpure_r P (⌜P⌝ -∗ H) (⌜P⌝ -∗ H))=>//
    apply hhimpl_refl
    apply hhwand_cancel }
  srw hhwand_equiv
  sby apply hhimpl_hstar_hhpure_l=> ??

lemma hhwand_curry (H1 H2 H3 : hhProp) :
  (H1 ∗ H2) -∗ H3 ==> H1 -∗ (H2 -∗ H3) :=
by
  sdo 2 apply hhimpl_hhwand_r;
  srw -hhstar_assoc [0]hhstar_comm
  apply hhwand_cancel

lemma hhwand_uncurry (H1 H2 H3 : hhProp) :
  H1 -∗ (H2 -∗ H3) ==> (H1 ∗ H2) -∗ H3 :=
by
  srw hhwand_equiv [2]hhstar_comm hhstar_assoc
  apply hhimpl_hhstar_trans_r
  sdo 2 apply hhwand_cancel;

lemma hhwand_curry_eq (H1 H2 H3 : hhProp) :
  (H1 ∗ H2) -∗ H3 = H1 -∗ (H2 -∗ H3) :=
by
  apply hhimpl_antisymm
  { apply hhwand_curry }
  apply hhwand_uncurry

lemma hhwand_inv (h1 h2 : hheap) (H1 H2 : hhProp) :
  (H1 -∗ H2) h2 →
  H1 h1 →
  hdisjoint h1 h2 →
  H2 (h1 ∪ h2) :=
by
  move=> [? ![hW1 ?? [/hhimpl h1W hW2emp] /hW2emp /hunion_empty hU *]]
  apply h1W ; exists h1, hW1
  sby srw hU

/- --------------------- Properties of [hhtop] --------------------- -/

lemma hhtop_intro (h : hheap) :
  ⊤ h :=
by sdone

lemma hhimpl_hhtop_r {H : hhProp} :
  H ==> ⊤ :=
by sdone

lemma hhtop_eq :
  (⊤ : hhProp) = ∃ʰ H, H :=
by
  srw hhtop

lemma hhstar_hhtop_hhtop :
  (⊤ : hhProp) ∗ (⊤ : hhProp) = (⊤ : hhProp) :=
by
  apply hhimpl_antisymm
  { apply hhimpl_hhtop_r }
  srw -[1](@hhstar_hhempty_r _ ⊤)
  apply hhimpl_frame_r ; apply hhimpl_hhtop_r

/- -------------------- Properties of [bighstar] -------------------- -/

lemma union_nonmem (f₁ f₂ : heap) (p : loc) :
  p ∉ f₁ ∪ f₂ → p ∉ f₁ ∧ p ∉ f₂ := by
  sby unfold Not

lemma union0 (f₁ f₂ : heap) :  f₁ ∪ f₂ = ∅ <-> f₁ = ∅ ∧ f₂ = ∅ := by
  apply Iff.intro
  { move=> ?
    apply And.intro <;> apply Finmap.ext_lookup=> > /=
    all_goals have hx:(x ∉ f₁ ∪ f₂) := by sdone ;
    srw Finmap.lookup_eq_none
    sby move: hx=> /union_nonmem }
  sby move=> [] -> ->

lemma bighstar_intro (s : Set α) (H : α -> hProp) :
  (forall i, H i (h i)) -> [∗ i in s | H i] (extend s h) := by
    sby move=> Hh a; unfold extend; scase_if

lemma bighstarDef_split {s : Set α} (Hh : α -> hProp) h₀:
  bighstarDef s Hh h₀ h ->
    (∀ a ∈ s, Hh a (h a)) ∧ (∀ a ∉ s, h a = h₀ a) := by
    sby move=> H ⟨|⟩ a inS <;> move: (H a) <;> scase_if


lemma bighstar_split {s : Set α} (Hh : α -> hProp):
  [∗ i in s| Hh i] h ->
    (∀ a ∈ s, Hh a (h a)) ∧ (∀ a ∉ s, h a = ∅) := by
    sby move=> H ⟨|⟩ a inS <;> move: (H a) <;> scase_if

lemma bighstarDef_eq :
  bighstarDef s (fun a => (· = hh a)) hh = (· = hh) := by
  apply hhimpl_antisymm=> [? /= h !a |?->?]
  { sby move: (h a); scase_if }
  sby scase_if

macro_rules | `(tactic| ssr_triv) => `(tactic| solve_by_elim)
lemma bighstarDef_hhstar
   {hH₁ hH₂ : α ->  hProp} {s : Set α}:
    hdisjoint h₁ h₂ ->
    (bighstarDef s hH₁ h₁) ∗ (bighstarDef s hH₂ h₂) = bighstarDef s (fun i => hH₁ i ∗ hH₂ i) (h₁ ∪ h₂) := by
    move=> ?
    scase: (Set.eq_empty_or_nonempty s)=> [->|]
    { srw ?bighstarDef0; apply hhimpl_antisymm=> /==
      { sby move=> ? ![] }
      sby exists h₁, h₂ }
    move=> exS ! hh /== ⟨![hh₁ hh₂ h₁H h₂H ->? a]|H⟩
    { scase_if=> /== ?
      { exists (hh₁ a), (hh₂ a); repeat' constructor=> //
        { sby move: (h₁H a); scase_if }
        sby move: (h₂H a); scase_if }
      sby move: (h₁H a) (h₂H a); scase_if }
    scase: exS=> x ?
    scase: (bighstarDef_split _ _ H)=> /(choose_fun (hh x))[f₁]
    move=> /(choose_fun (hh x))[f₂] H ?
    let h₁ := fun a => if a ∈ s then f₁ a else h₁ a
    let h₂ := fun a => if a ∈ s then f₂ a else h₂ a
    exists h₁, h₂
    repeat' constructor; simp [h₁, h₂]
    { sby move=> ?; scase_if }
    { sby move=> ?; scase_if }
    { sby ext1=> /=; scase_if }
    sby move=> ?; simp [h₁, h₂]; scase_if

lemma bighstar_hhstar
   {hH₁ hH₂ : α ->  hProp} {s : Set α}:
    [∗ i in s | hH₁ i] ∗ [∗ i in s | hH₂ i] = [∗ i in s | hH₁ i ∗ hH₂ i] := by
    sby srw ?bighstar bighstarDef_hhstar; congr=> ?

lemma bighstar_hhstar_disj
   {hH : α -> hProp} {s₁ s₂ : Set α} :
    Disjoint s₁ s₂ ->
    [∗ i in s₁ | hH i] ∗ [∗ i in s₂ | hH i] = [∗ i in s₁ ∪ s₂ | hH i] := by
    move=> /Set.disjoint_left Dij !hh /== ⟨![hh₁ hh₂ Hh₁ Hh₂ -> ? a/==]|⟩
    { scase_if=> /== <;> move: (Hh₁ a) (Hh₂ a)=> /== <;> scase_if
      { sby move=> /Dij; scase_if }
      { sby move=> ? -> /==; scase_if }
      { sby move=> /Dij; scase_if }
      sby scase_if }
    let h₁ := fun a => if a ∈ s₁ then hh a else ∅
    let h₂ := fun a => if a ∈ s₂ then hh a else ∅
    move=> H; exists h₁, h₂; (repeat' constructor) <;> simp [h₁, h₂]
    { sby move=> a /=; move: (H a)=> /==; sdo 2 scase_if }
    { sby move=> a /=; move: (H a)=> /==; sdo 2 scase_if }
    { move=> !a/=; scase_if=> [/Dij|/==] <;> scase_if=> //
      sby move: (H a)=> /==; scase_if }
    move=> a; sdo 2 scase_if=> // *
    { apply Finmap.Disjoint.symm; apply Finmap.disjoint_empty }
    apply Finmap.disjoint_empty

lemma bighstarDef_hexists [Inhabited β] {P : α -> β -> hProp} {hh₀ : hheap} :
  bighstarDef s (fun a => hexists (P a)) hh₀  = ∃ʰ (x : α -> β), bighstarDef s (fun a => P a (x a)) hh₀ := by
  apply hhimpl_antisymm
  { move=> hh hhH; unfold hhexists=> /=
    srw -(skolem (p := fun a v => if a ∈ s then P a v (hh a) else hh a = hh₀ a))=> x
    scase: [x ∈ s]=> xin
    { exists default; srw if_neg
      sby move: (hhH x); srw if_neg }
    sby move: (hhH x); srw if_pos }
  sby move=> j [x] /= /[swap] a /(_ a); scase_if

lemma bighstar_hexists [Inhabited β] {P : α -> β -> hProp} :
  bighstar s (fun a => hexists (P a))  = ∃ʰ (x : α -> β), bighstar s (fun a => P a (x a)) := by
  apply bighstarDef_hexists


lemma bighstarDef_himpl (s : Set α) (H H' : α -> hProp) :
  (∀ a ∈ s, himpl (H a) (H' a)) -> bighstarDef s H h₀ ==> bighstarDef s H' h₀ := by
  sby move=> himp ? Hh a; move: (Hh a); scase_if

lemma bighstarDef_def_eq  :
  (∀ a ∉ s, h₀ a = h₀' a) →
  bighstarDef s H h₀ = bighstarDef s H h₀' := by
  move=> eq
  sby apply hhimpl_antisymm=> h /[swap] a /(_ a) M <;> scase_if

lemma bighstar_himpl (s : Set α) (H H' : α -> hProp) :
  (∀ a ∈ s, himpl (H a) (H' a)) -> [∗ i in s | H i] ==> [∗ i in s | H' i] := by
  sby apply bighstarDef_himpl

lemma bighstarDef_hpure (s : Set α) (P : α -> Prop) :
  bighstarDef s (hpure ∘ P) ∅ = ⌜∀ i ∈ s, P i⌝ := by
    apply hhimpl_antisymm
    { move=> h H ⟨|⟩/=
      { sby move=> i; move: (H i); scase_if=> // ? [] }
      sby move=> !a; move: (H a); scase_if=> // ? [] }
    sby move=> h []/= ? -> ?; scase_if

lemma bighstar_hpure_nonemp (s : Set α) (P : Prop) :
  s.Nonempty ->
  [∗ in s | hpure P] = ⌜P⌝ := by
  move=> [σ In]; apply hhimpl_antisymm
  { move=> h H; move: (H σ); scase_if=> //_
    scase=> p /= ?; exists p=> /= ! σ
    sby move: (H σ); scase_if=> // ? []? }
  sby move=> h []p /=-> ?; scase_if

/- -------------------- Properties of [hhsingle] -------------------- -/

variable (s : Set α)

lemma hhsingle_intro (p : α -> _) (v : α -> _) :
  (p i ~⟨i in s⟩~> v i) (extend s (fun i =>Finmap.singleton (p i) (v i))) :=
by apply bighstar_intro; sdone

lemma hhsingl_inv p v h :
  (p ~(s)~> v) h →
  h = extend s (fun _ => Finmap.singleton p v) :=
by sby move=> sH ! z; move: (sH z); unfold extend; scase_if



lemma hhstar_hhsingle_same_loc (p : α -> _) (v1 v2 : α -> _) :
  s.Nonempty ->
  (p i ~⟨i in s⟩~> v1 i) ∗ (p i ~⟨i in s⟩~> v2 i) ==> ⌜False⌝ :=
by
  move=> ?; srw bighstar_hhstar
  apply (@hhimpl_trans (h₂ := [∗ in s | hpure False]))
  { apply bighstar_himpl=> ??; apply hstar_hsingle_same_loc }
  sby srw bighstar_hpure_nonemp

end HHProp

/- ------------- Abstract Hyper Separation Logic Theory ------------- -/

section AbstractSepLog

def hhadd [PartialCommMonoid val] (H₁ H₂ : hhProp α) : hhProp α :=
  fun h => exists h1 h2, H₁ h1 ∧ H₂ h2 ∧ h = h1 +ʰ h2 ∧ h1 ⊥ʰ h2

instance : Zero (hhProp α) := ⟨emp⟩
instance [PartialCommMonoid val] : Add (hhProp α) := ⟨hhadd⟩

attribute [-simp] hValidInter

instance [PartialCommMonoid val] : AddCommMonoid (hhProp α) where
  zero := emp
  add  := hhadd
  nsmul := nsmulRec
  add_comm  := by
    move=> H₁ H₂ !h !⟨|⟩![h₁ h₂ ?? /hHeap.add_comm -> /hValidInter_symm ?]
    <;> exists h₂, h₁
  add_assoc := by
    move=> H₁ H₂ H₃ !h !⟨![h₁ h₃ ![h₁ h₂] ??-> ?? -> /hValidInter_add_left [] ??]|⟩
    { exists h₁, (h₂ +ʰ h₃); sdo 3 constructor=> //
      srw hHeap.add_assoc }
    scase! => h₁ h₂  ? ![h₂ h₃ ??-> ? -> /hValidInter_add_right []??]
    exists (h₁ +ʰ h₂), h₃; sdo 3 constructor=> //
    srw hHeap.add_assoc
  add_zero  := by
    move=> H !h !⟨![?? ? -> //]|?⟩
    exists h, ∅ ; sdo 3 constructor=> //
    move=> ?; apply validInter_empty_r
  zero_add  := by
    move=> H !h !⟨![?? -> ? //]|?⟩
    exists ∅, h; sdo 3 constructor=> //
    move=> ?; apply validInter_empty_l

instance [PartialCommMonoidWRT val add valid] : AddCommMonoidWRT (hhProp α) hhadd where
  addE := by sdone

namespace EmptyPCM

@[simp]
def hhaddE : (fun (H₁ H₂ : hhProp α) => H₁ + H₂) = (fun (H₁ H₂ : hhProp α) => H₁ ∗ H₂) := by
  move=> !H₁ !H₂ !h ! ⟨|⟩ ![h₁ h₂] ?? -> ? <;> exists h₁, h₂; sdo 4 constructor=> //
  { move=> !a; srw /== Heap.add_union_validInter // }
  { move=> a /==; srw -validInter_disjoint // }
  { move=> !a; srw /== Heap.add_union_validInter //
    srw validInter_disjoint // }
  move=> ?; srw validInter_disjoint //


instance (priority := high) : AddCommMonoidWRT hProp hadd where
  addE := by rfl

end EmptyPCM


end AbstractSepLog
