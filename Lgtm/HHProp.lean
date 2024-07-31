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

def hextend (s : Set α) [DecidablePred (· ∈ s)]  (h : heap) : hheap :=
  λ a => if a ∈ s then h else ∅

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

def hhextend (s : Set α) [DecidablePred (· ∈ s)]  (hH : hProp) : hhProp :=
  fun hh => ∃ h, hH h ∧ hh = hextend s h

notation "[in" s "| " h "]" => hhextend s h

def hhempty : hhProp := (· = ∅)

notation:max "emp" => hhempty

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
  hhexists (fun (H : hhProp) => H)

def hhwand (H1 H2 : hhProp) : hhProp :=
  hhexists (fun (H0 : hhProp) => H0 ∗ (hhpure (H1 ∗ H0 ==> H2)))

@[default_instance]
instance : HWand hhProp hhProp hhProp := ⟨hhwand⟩

def hqwand {A} (Q1 Q2 : A → hhProp) : hhProp :=
  hhforall (fun (x : A) => (Q1 x) -∗ (Q2 x))

notation:max "⌜" P "⌝" => hhpure P

/- ⊤⊤ is very annoynig, let's just overwrite lean's ⊤ -/
notation (priority := high) "⊤" => hhtop

def hqstar {A} (Q : A → hhProp) (H : hhProp) : A → hhProp :=
  fun x => (Q x) ∗ H

instance (A : Type) : HStar (A → hhProp) hhProp (A → hhProp) where
  hStar := hqstar

instance (α : Type) : HWand (α → hhProp) (α → hhProp) hhProp where
  hWand := hqwand


end HHProp
