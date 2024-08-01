import Mathlib.Data.Finmap

import Lgtm.Util
import Lgtm.HProp


open Classical

section HHProp

variable {α : Type} [DecidableEq α]

abbrev hheap := α -> heap
abbrev hhProp := @hheap α -> Prop

local notation "hhProp" => @hhProp α
local notation "hheap" => @hheap α

def hEmpty : hheap := fun _ => ∅

instance : EmptyCollection hheap := ⟨hEmpty⟩

def hSingle (a : α) (p : loc) (v : val) : hheap :=
  λ a' => if a = a' then Finmap.singleton p v else ∅

-- def hextend (s : Set α) [DecidablePred (· ∈ s)]  (h : heap) : hheap :=
--   λ a => if a ∈ s then h else ∅

def hunion (h₁ h₂ : hheap) : hheap :=
  λ a => h₁ a ∪ h₂ a

instance : Union hheap := ⟨hunion⟩

@[simp]
lemma unionE {h₁ h₂ : hheap} {a : α} : (h₁ ∪ h₂) a = h₁ a ∪ h₂ a := by rfl

@[simp]
def hdisjoint (h₁ h₂ : hheap) : Prop :=
  ∀ a, Finmap.Disjoint (h₁ a) (h₂ a)


abbrev hhimpl (H₁ H₂ : hhProp) : Prop :=
  forall h, H₁ h -> H₂ h

infixr:51 " ==> " => hhimpl

def hqimpl {A} (Q₁ Q₂ : A → hhProp) : Prop :=
  forall (v:A), Q₁ v ==> Q₂ v

infixr:51 " ===> " => hqimpl

-- variable (hH₁ hH₂ : hhProp)

def hextend (s : Set α) (hH : hProp) : hhProp :=
  fun hh => ∀ a, if a ∈ s then hH (hh a) else hh a = ∅

notation "[in " s "| " h "]" => hextend s h

def hhempty : hhProp := (· = ∅)

notation:max (priority := high) "emp" => hhempty

def hhsingle (a : α) (p : loc) (v : val) : hhProp := [in {a} | p ~~> v]

notation p " ~" s:max "~> " v => [in s | p ~~> v]


def hhstar (hH₁ hH₂ : hhProp) : hhProp :=
  fun (hh : hheap) =>
    exists (hh₁ hh₂ : hheap),
      hH₁ hh₁ ∧ hH₂ hh₂ ∧ hh = hh₁ ∪ hh₂ ∧ hdisjoint hh₁ hh₂

@[default_instance]
instance : HStar hhProp hhProp hhProp := ⟨hhstar⟩

def hhexists {A} (P : A → hhProp) : hhProp :=
  fun hh => exists (v:A), P v hh

def hhforall {A} (P : A → hhProp) : hhProp :=
  fun hh => forall (v:A), P v hh

section
open Lean.TSyntax.Compat
macro "h∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hhexists xs b
macro "h∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hhforall xs b
end

@[app_unexpander hhexists] def unexpandHHExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∃ $xs:binderIdent*, $b) => `(h∃ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∃ ($x:ident : $t), $b)
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

notation:max "⌜" P "⌝" => hhpure P

/- ⊤⊤ is very annoynig, let's just overwrite lean's ⊤ -/
notation (priority := high) "⊤" => hhtop

def hqstar {A} (q : A → hhProp) (h : hhProp) : A → hhProp :=
  fun x => (q x) ∗ h

instance (A : Type) : HStar (A → hhProp) hhProp (A → hhProp) where
  hStar := hqstar

instance (α : Type) : HWand (α → hhProp) (α → hhProp) hhProp where
  hWand := hqwand

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

lemma hhempty_hextend0 : [in ∅ | h] = (emp : hhProp) :=
  by sby unfold hhempty hextend=> !? /== ⟨?!|->⟩

lemma hhempty_hextend_emp (s : Set α) [DecidablePred (· ∈ s)] : [in s | hempty] = emp :=
  by sby unfold hhempty hextend=> !?; simp[hempty]=> ⟨?!|->⟩



/- ---------------- Properties of [hstar] ---------------- -/

lemma hhstar_intro : ∀ {hH₁ hH₂ : hhProp} {h₁ h₂ : hheap}, hH₁ h₁ -> hH₂ h₂ ->
  hdisjoint h₁ h₂ -> (hH₁ ∗ hH₂) (h₁ ∪ h₂) :=
  by sdone

lemma hhstar_inv {hH₁ hH₂ : hhProp} {h : hheap} : (hH₁ ∗ hH₂) h ->
  exists (h₁ h₂ : hheap), hH₁ h₁ ∧ hH₂ h₂ ∧ h = h₁ ∪ h₂ ∧ hdisjoint h₁ h₂ :=
  by sapply

lemma hhstar_comm {hH₁ hH₂ : hhProp} : hH₁ ∗ hH₂ = hH₂ ∗ hH₁ :=
  by apply hhprop_op_comm=> > ? ![>??] ->; sorry

lemma hhstar_assoc {hH₁ hH₂ hH₃ : hhProp} : hH₁ ∗ (hH₂ ∗ hH₃) = (hH₁ ∗ hH₂) ∗ hH₃ := by sorry

lemma hhstar_hempty_l {hH : hhProp} : emp ∗ hH = hH :=
  by sorry

lemma hhstar_hempty_r {hH : hhProp} : hH ∗ emp = hH :=
  by sorry

lemma hhstar_hhexists_l {A} {P : A → hhProp} {hH : hhProp} :
  (hhexists P) ∗ hH = hhexists (fun x => P x ∗ hH) :=
  by sorry

lemma hhstar_hhforall_l {A} {P : A → hhProp} {hH : hhProp} :
  (hhforall P) ∗ hH = hhforall (fun x => P x ∗ hH) :=
  by sorry

lemma hhimpl_frame_l (hH₁ hH₂ hH₃ : hhProp) : hH₁ ==> hH₂ -> hH₁ ∗ hH₃ ==> hH₂ ∗ hH₃ :=
  by sorry

lemma hhimpl_frame_r (hH₁ hH₂ hH₃ : hhProp) : hH₁ ==> hH₂ -> hH₃ ∗ hH₁ ==> hH₃ ∗ hH₂ :=
  by sorry

lemma hhimpl_frame_lr (hH₁ hH₂ hH₃ hH₄ : hhProp) : hH₁ ==> hH₂ -> hH₃ ==> hH₄ -> hH₁ ∗ hH₃ ==> hH₂ ∗ hH₄ :=
  by sorry

/- --------------- Properties of [hhpure] --------------- -/
/- ----------------- Properties of [hhexists] ----------------- -/
/- ----------------- Properties of [hqwand] ----------------- -/
/- --------------------- Properties of [hhtop] --------------------- -/
/- -------------------- Properties of [hhsingle] -------------------- -/
/- -------------------- Properties of [hhsingle] -------------------- -/
/- -------------------- Properties of [hextend] -------------------- -/

lemma union0 (f₁ f₂ : heap) :  f₁ ∪ f₂ = ∅ <-> f₁ = ∅ ∧ f₂ = ∅ := by sorry

-- lemma ex_hheap (hH : hProp) {s : Set α} [DecidablePred (· ∈ s)] :
--   [in s | hH] h -> ∃ h : hheap, fora


lemma choose_fun {α β : Type} (b₀ : β)  (p : α -> β -> Prop) (s : Set α) :
  (∀ a ∈ s, ∃ b : β, p a b) -> (∃ f : α -> β, (∀ a ∈ s, p a (f a))) := by
  move=> pH
  exists (fun a => if h : a ∈ s then choose (pH a h) else b₀)=> /=
  move=> a inS
  srw dif_pos //; apply choose_spec

lemma hextend_split {s : Set α} :
  [in s| Hh] h ->
    (∀ a ∈ s, Hh (h a)) ∧ (∀ a ∉ s, h a = ∅) := by
    sby move=> H ⟨|⟩ a inS <;> move: (H a) <;> scase_if

macro_rules | `(tactic| ssr_triv) => `(tactic| solve_by_elim)
lemma hexted_hstar
   {hH₁ hH₂ : hProp} {s : Set α} :
    [in s | hH₁] ∗ [in s | hH₂] = [in s | hH₁ ∗ hH₂] := by
    scase: (Set.eq_empty_or_nonempty s)=> [->|]
    { sby srw ?hhempty_hextend0 hhstar_hempty_l }
    move=> exS ! hh /== ⟨![> h₁H h₂H ->? a]|H⟩
    { scase_if=> /== ?
      { (sdo 5 econstructor)=> //
        { sby move: (h₁H a); scase_if }
        sby move: (h₂H a); scase_if }
      srw union0; constructor
      { sby move: (h₁H a); scase_if }
      sby move: (h₂H a); scase_if }
    scase: exS=> x ?
    scase: (hextend_split H)=> /(choose_fun (hh x))[f₁]
    move=> /(choose_fun (hh x))[f₂] H ?
    let h₁ := fun a => if a ∈ s then f₁ a else ∅
    let h₂ := fun a => if a ∈ s then f₂ a else ∅
    exists h₁; exists h₂
    repeat' constructor; simp [h₁, h₂]
    { sby move=> ?; simp [h₁]; scase_if }
    { sby move=> ?; simp [h₂]; scase_if }
    { sby ext1=> /=; scase_if }
    sby move=> ?; simp [h₁, h₂]; scase_if

end HHProp
