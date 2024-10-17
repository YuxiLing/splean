import Lean

import Mathlib.Data.Finmap
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval

import Ssreflect.Lang

open Classical

abbrev loc := Nat
abbrev var := String


abbrev Heap.heap (val : Type) := Finmap (λ _ : loc ↦ val)

class PartialCommMonoid (α : Type) extends AddCommSemigroup α where
  valid : α -> Prop
  valid_add : ∀ x, valid (x + y) -> valid x


class PartialCommMonoidWRT (α : Type) (add' : semiOutParam (α -> α -> α)) (valid' : semiOutParam (α -> Prop)) extends PartialCommMonoid α where
  addE : (· + ·) = add'
  validE : PartialCommMonoid.valid = valid'

open PartialCommMonoid (valid)

section

variable {val : Type} [PartialCommMonoid val] [Inhabited val]

local notation "heap" => Heap.heap val

@[simp]
noncomputable def kmerge : List (Sigma (fun _ : loc => val)) → List (Sigma (fun _ : loc => val)) → List (Sigma (fun _ : loc => val))
  | [], l₂ => l₂
  | s :: l₁, l₂ =>
    (if s.1 ∈ l₂.keys then
      ⟨s.1, s.2 + (l₁.find? (·.1 = s.1)).get!.2⟩ :: kmerge l₁ (l₂.kerase s.1)
    else s :: kmerge l₁ l₂)

-- #check List.kerase

-- @[simp]
-- lemma kerase_mem (l₂ : List (Sigma (fun _ : loc => val))) :
--   l₁ ∈ l₂.keys ->
--   l ∈ (List.kerase l₁ l₂).keys ↔ l ≠ l₁ ∧ l ∈ l₂.keys :=
--   by
--     elim: l₂ l₁=> //== l' v l ih  l₁
--     { scase: [l₁ = l']=> [?|->]
--       { srw List.kerase_cons_ne //== ih => ⟨|⟩// [] // -> ⟨|⟩ // ? // }
--       srw List.kerase_cons_eq // =>  }

@[simp]
lemma kmerge_mem (l₁ : List (Sigma (fun _ : loc => val))) : l ∈ (kmerge l₁ l₂).keys ↔ l ∈ l₁.keys ∨ l ∈ l₂.keys :=
  by
    elim: l₁ l₂=> // [] /= l' v l₁ ih l₂
    scase: [l' ∈ l₂.keys]=> /=
    { srw /== ih => ? ⟨[|[]]|[[]|]⟩ // }
    move=> ?; scase: [l = l']=> [?|->] /==
    srw ih List.mem_keys_kerase_of_ne /== //

noncomputable def AList.merge (h₁ h₂ : AList (fun _ : loc => val)) :  AList (fun _ : loc => val) :=
  ⟨kmerge h₁.entries h₂.entries, by
    scase: h₁ h₂=> /= e₁ /[swap] [] /=
    elim: e₁=> /== [] l v e₁ ih e₂ ???
    split_ifs=> /== ⟨|⟩ //; apply ih=> //; apply List.NodupKeys.kerase=> //⟩

theorem Perm.kmerge {l₁ l₂ l₃ l₄ : List (Sigma (fun _ : loc => val))} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁.Perm l₂)
    (p₃₄ : l₃.Perm l₄) : (kmerge l₁ l₃).Perm $ kmerge l₂ l₄ := sorry



noncomputable def Heap.add (h₁ h₂ : heap) : heap :=
  Finmap.liftOn₂ h₁ h₂ (fun h₁ h₂ => (h₁.merge h₂).toFinmap) (by
    move=> > ??; srw AList.toFinmap_eq
    apply Perm.kmerge; apply AList.nodupKeys
    all_goals assumption)

infixr:55 " +ʰ " => Heap.add

@[simp]
lemma Heap.add_lookup (h₁ h₂ : heap) (l : loc) :
  (h₁ +ʰ h₂).lookup l =
    if l ∈ h₁ then
      if l ∈ h₂ then do (<- h₁.lookup l) + (<- h₂.lookup l)
      else h₁.lookup l
    else h₂.lookup l := by sorry

@[simp]
lemma Heap.add_mem (h₁ h₂ : heap) : (l ∈  h₁ +ʰ h₂) = (l ∈ h₁ ∨ l ∈ h₂) := by sorry

@[simp]
lemma Heap.add_empty_r (h : heap) : h +ʰ ∅ = h := by sorry

@[simp]
lemma Heap.add_empty_l (h : heap) : ∅ +ʰ h = h := by sorry

lemma Heap.add_comm (h₁ h₂ : heap) : h₁ +ʰ h₂ = h₂ +ʰ h₁ := by sorry

lemma Heap.add_assoc (h₁ h₂ h₃ : heap) : (h₁ +ʰ h₂) +ʰ h₃ = h₁ +ʰ h₂ +ʰ h₃ := by sorry

def validLoc (l : loc) (h : heap) : Prop := (h.lookup l).any (valid (α := val))

def validInter (h₁ h₂ : heap) : Prop :=
  ∀ l ∈ h₁, l ∈ h₂ -> validLoc l h₁ ∧ validLoc l h₁

lemma Heap.addE_of_disjoint [PartialCommMonoid val] (h₁ h₂ : heap) :
  h₁.Disjoint h₂ ->  h₁ +ʰ h₂ = h₁ ∪ h₂ := by
  move=> dj; apply Finmap.ext_lookup=> l /==
  scase_if=> [/dj ?|/Finmap.lookup_union_right//]
  srw if_neg //; srw Finmap.lookup_union_left_of_not_in //

infixr:55 " ⊥ʰ " => validInter

lemma validInter_comm (h₁ h₂ : heap) :
  h₁ ⊥ʰ h₂ = h₂ ⊥ʰ h₁ := by sorry

lemma validInter_empty_r (h : heap) : h ⊥ʰ ∅ := by sorry

lemma validInter_empty_l (h : heap) : ∅ ⊥ʰ h := by sorry

@[simp]
lemma disjoint_add_eq [PartialCommMonoid val] (h₁ h₂ h₃ : heap) :
  (h₁ +ʰ h₂).Disjoint h₃ = (h₁.Disjoint h₃ ∧ h₂.Disjoint h₃) := by
  move=> !⟨dj⟨|⟩|[dj₁ dj₂]⟩ l /==
  { move: (dj l)=> // }
  { move: (dj l)=> // }
  scase=> [/dj₁|/dj₂] //

@[simp]
lemma validInter_hop_eq_r (h₁ h₂ h₃ : heap) :
  (h₁ +ʰ h₂) ⊥ʰ h₃ = (h₁ ⊥ʰ h₃ ∧ h₂ ⊥ʰ h₃) := by sorry

@[simp]
lemma validInter_hop_eq_l (h₁ h₂ h₃ : heap) :
  h₁ ⊥ʰ (h₂ +ʰ h₃) = (h₁ ⊥ʰ h₂ ∧ h₁ ⊥ʰ h₃) := by sorry

lemma validInter_of_disjoint (h₁ h₂ : heap) :
  h₁.Disjoint h₂ ->  h₁ ⊥ʰ h₂ := by sorry

end

namespace EmptyPCM

variable {val : Type} [Inhabited val]

abbrev add : val -> val -> val := fun _ _ => default
abbrev valid : val -> Prop := fun _ => False

scoped instance (priority := low) : AddCommSemigroup val where
  add := add
  add_assoc := by sdone
  add_comm := by sdone

scoped instance (priority := 1) EPCM : PartialCommMonoid val where
  valid := valid
  valid_add := by sdone

scoped instance (priority := 0) EPCM' : PartialCommMonoidWRT val add valid where
  addE := by sdone
  validE := by sdone

@[simp]
lemma validE : PartialCommMonoid.valid (α := val) = fun _ => False := by sdone

@[simp]
lemma validLocE : validLoc (val := val) l h = False := by
  srw validLoc; scase: (Finmap.lookup l h)=> //==


lemma validInter_disjoint (h₁ h₂ : Heap.heap val) :
  h₁ ⊥ʰ h₂ = h₁.Disjoint h₂ := by
  srw validInter /==; rfl

@[simp]
lemma Heap.add_union_validInter (h₁ h₂ : Heap.heap val) {_ : h₁ ⊥ʰ h₂} :
  h₁ +ʰ h₂ = h₁ ∪ h₂ := by sorry

end EmptyPCM

notation "⟦" z ", " n "⟧" => Finset.Ico (α := ℤ) z n

lemma sum_Ico_succl {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i in ⟦i, j⟧, f i = f i + ∑ i in ⟦i+1, j⟧, f i := by sorry

lemma sum_Ico_succlr {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  ∑ i in ⟦i, j⟧, f (i+1) = ∑ i in ⟦i+1, j+1⟧, f i := by sorry

lemma sum_Ico_predr {_ : AddCommMonoid M} (f : Int -> M) (i j : Int) :
  i < j ->
  ∑ i in ⟦i, j⟧, f i = (∑ i in ⟦i, j - 1⟧, f i) + f (j -1) := by sorry
