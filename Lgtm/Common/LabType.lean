import Lean
import Mathlib.Data.Finmap

import Lgtm.Common.Util

-- abbrev LabType := ℕ
local macro "LabType" : term => `(ℕ)

structure Labeled (α : Type*) where
  lab : LabType
  val : α

instance [Inhabited α] : Inhabited (Labeled α) := ⟨⟨0, default⟩⟩

def labSet (l : ℕ) (s : Set α) : Set (Labeled α) := { ⟨l, x⟩ | x ∈ s }

notation (priority := high) "⟪" l ", " s "⟫" => labSet l s

@[disjE]
lemma disjoint_label_set :
  Disjoint ⟪l,s⟫ ⟪l',s'⟫ ↔ l ≠ l' ∨ Disjoint s s' := by
  sorry

@[simp]
lemma labSet_inter (l : ℕ) (s s' : Set α) :
  ⟪l, s⟫ ∩ ⟪l, s'⟫ = ⟪l, s ∩ s'⟫ := by
  sorry

@[simp]
lemma labSet_diff (l : ℕ) (s s' : Set α) :
   ⟪l, s⟫ \ ⟪l, s'⟫ = ⟪l, s \ s'⟫ := by
  sorry

@[simp]
lemma labSet_mem :
  x ∈ ⟪l, s⟫ ↔ x.lab = l ∧ x.val ∈ s := by
  sorry
