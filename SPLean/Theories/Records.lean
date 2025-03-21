import SPLean.Theories.XSimp
import SPLean.Theories.XChange
import SPLean.Common.Util
import SPLean.Theories.SepLog
import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.Arrays

open Classical


open trm val Theories

abbrev field : Type := ℕ

def hfield (p : loc) (k : field) (v : val) : hProp  :=
  (p + 1 + k) ~~> v

notation:100 p:100 ". " k:100 " ~~> " v:0 => hfield p k v

abbrev hrecord_field: Type := field × val
abbrev hrecord_fields : Type := List hrecord_field


notation "`{" k1 " := " v1 "}" => [(k1, (v1 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "}" => [(k1, (v1 : val)), (k2, (v2 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "; " k3 " := " v3 "}" => [(k1, (v1 : val)), (k2, (v2 : val)), (k3, (v3 : val))]

def hfields (kvs : hrecord_fields) (p:loc): hProp :=
  match kvs with
  | [] => ⌜True⌝
  | (ki, vi) :: kvs' => (p. ki ~~> vi) ∗ (hfields kvs' p)
-- axiom hrecord : hrecord_fields → loc → hProp


--notation p " ~~~> " kvs => hrecord kvs p

--axiom hrecord_not_null : ∀ (p : loc) (kvs : hrecord_fields), hrecord kvs p ==> hrecord kvs p ∗  ⌜p ≠ null⌝

-- Read Operation on Record fields
--axiom val_get_field : field → val




def maps_all_fields (n:ℕ) (kvs:hrecord_fields) : Prop :=
  List.map Prod.fst kvs =  List.range' 0 n

def hrecord (kvs:hrecord_fields) (p:loc) : hProp :=
  ∃ʰ (n:ℕ), hheader n p ∗ hfields kvs p ∗ ⌜maps_all_fields n kvs⌝

notation p " ~~~> " kvs => hrecord kvs p

lemma hrecord_elim_aux (kvs:hrecord_fields)
 :
  ∀ (s n:ℕ),
  ((List.map Prod.fst kvs) = List.range' s n  ) →
(List.length kvs) = n :=
by
  induction kvs with
  | nil =>
    intro a b H
    simp at H
    symm at H
    --simp[List.range'_eq_nil] at H
    aesop
  | cons x xs Ih =>
    intro s n H
    simp at H
    cases n with
    | zero =>
      have hh : List.range' s 0 = List.nil := by simp[List.range'_eq_nil]
      rw[hh] at H
      simp at H
    | succ n' =>
     rw[←List.range'_append] at H
     simp at H
     simp[Ih _ _ (And.right H)]


lemma hrecord_elim : ∀ p kvs,
  hrecord kvs p ==> hheader (List.length kvs) p ∗ hfields kvs p :=
by
  intro p kvs
  unfold hrecord
  xpull
  intros z Hz
  xsimp
  apply himpl_of_eq
  unfold maps_all_fields at Hz
  simp[hrecord_elim_aux kvs 0 z Hz]



def head : field := 0
def tail : field := 1

open trm prim

/-
def val_get_field  (k: field): val :=
 [lang|
 fun p =>
    let p1 := p ++ 1 in
    let q := p1 ++ ⟨Int.ofNat k⟩ in
    !q]
-/

notation t1 "!." k:1525 => (val_get_field k) t1

lemma triple_get_field : ∀ (p:loc) (k: field) v,
  triple [lang| ⟨val_get_field k⟩ p]
    (p. k ~~> v)
    (fun r => ⌜r = v⌝  ∗ (p. k ~~> v))
:=
by
    xwp
    unfold hfield
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby xapp


def val_set_field  (k: field): val :=
 [lang|
 fun p v =>
    let p1 := p ++ 1 in
    let q := p1 ++ ⟨Int.ofNat k⟩ in
     q := v ]


lemma triple_set_field : ∀ (p:loc) (k: field) v1 v2  ,
  triple [lang| ⟨val_set_field k⟩ p v2]
    (p. k ~~> v1)
    (fun _ => (p. k ~~> v2))
:=
by
    xwp
    unfold hfield
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby xapp

-- notation t1:5120 "." k:5120 " := " v:5120 => (val_set_field k) t1 v

syntax:max lang noWs "." noWs ident : lang

macro_rules
  | `([lang| $rcrd.$f ])              =>
    `(trm_val (val_get_field $f) [lang| $rcrd])
  | `([lang| $rcrd.$f := $v ])        => `(trm_val (val_set_field $f) [lang| $rcrd] [lang| $v])

example (t : loc) (f : field) : trm := [lang| t.f]


def hfields_lookup (k : field) (kvs : hrecord_fields) : Option val :=
  match kvs with
  | [] => none
  | (ki, vi) :: kvs' => if k = ki then some vi else hfields_lookup k kvs'

lemma triple_get_field_hfields : ∀ kvs (p:loc) k v,
  hfields_lookup k kvs = some v →
  triple [lang| ⟨val_get_field k⟩ p]
    (hfields kvs p)
    (fun r => ⌜r = v⌝  ∗  hfields kvs p) :=
by
intro L
induction L with
| nil => intro _ _ _ contra; simp[hfields_lookup] at contra
| cons x L' ih =>
  intro p f v E
  simp[hfields_lookup] at E
  cases Classical.em (f = x.1) with
  | inl h =>
    simp[(if_pos h)] at E
    simp [←E]
    simp[h]
    apply triple_conseq_frame
    { apply triple_get_field; aesop }
    { simp[hfields]; xsimp }
    { xsimp; simp[hfields, qstarE]; xsimp }
  | inr h =>
    apply triple_conseq_frame
    simp[(if_neg h)] at E
    { apply (ih _ _ _ E) }
    { simp[hfields]; xsimp }
    { simp[hfields, qstarE]
      intro _; dsimp
      xsimp }


def hfields_update (k:field) (v:val) (kvs:hrecord_fields) : Option hrecord_fields :=
  match kvs with
  | List.nil => none
  | kivi::kvs' => match kivi with
                  | (ki, vi) => if k = ki
                       then some ((k,v)::kvs')
                       else match hfields_update k v kvs' with
                            | none => none
                            | some LR => some ((ki,vi)::LR)


lemma triple_set_field_hfields : ∀ kvs kvs' k (p:loc) v,
  hfields_update k v kvs = some kvs' →
  triple [lang| ⟨val_set_field k⟩ p v]
    (hfields kvs p)
    (fun _ => hfields kvs' p) :=
by
  intro kvs
  induction kvs with
  | nil => intro _ _ _ _ contra; simp[hfields_update] at contra
  | cons x kvs1 IH =>
    intro kvs' k p v E
    simp[hfields_update] at E
    cases Classical.em (k = x.1) with
    | inl h =>
      simp[(if_pos h)] at E
      simp [←E, h,hfields]
      apply triple_frame
      apply (triple_set_field p x.1 x.2 v)
    | inr h =>
      simp[(if_neg h)] at E
      split at E
      case h_1 a _ => simp at E
      case h_2 kvs'' HH =>
        simp at E
        simp[←E]
        apply triple_conseq_frame
        { apply (IH _ _ _ _ HH) }
        { simp[hfields]; xsimp }
        { simp[hfields, qstarE]; intro _; xsimp; xsimp }




lemma triple_get_field_hrecord : ∀ kvs (p:loc) k v,
  hfields_lookup k kvs = some v →
  triple [lang| p.k /-(⟨val_get_field k⟩ p)-/ ]
    (hrecord kvs p)
    (fun r => ⌜r = v⌝  ∗ hrecord kvs p) :=
by
  introv M
  unfold hrecord
  xtriple
  xpull
  intro z Hz
  xapp (triple_get_field_hfields  _ _ _ _ M)
  --xapp triple_get_field_hfields
  /-
  xapp_pre
  eapply xapp_lemma; eapply (triple_get_field_hfields  _ _ _ _ M)
  rotate_right; xapp_simp; hide_mvars=>//
  -- xapp (triple_get_field_hfields  _ _ _ _ M)-/
  xsimp
  { simp }
  { exact Hz }




lemma hfields_update_preserves_fields : ∀ kvs kvs' k v,
  hfields_update k v kvs = some kvs' →
  List.map Prod.fst kvs' = List.map Prod.fst kvs :=
by
  intros kvs
  induction kvs with
  | nil => intro _ _ _ contra; simp[hfields_update] at contra
  | cons kivi kvs1 ih =>
    intro kvs' k v E
    simp[hfields_update] at E
    split at E
    case cons.isTrue h => simp at E; simp[←E, h]
    case cons.isFalse h =>
      split at E
      case h_1 a _ => simp at E
      case h_2 kvs'' HH =>
        simp at E
        simp[←E]
        simp[←(ih _ _ _  HH)]

lemma hfields_update_preserves_maps_all_fields : ∀ kvs kvs' z k v,
  hfields_update k v kvs = some kvs' →
  maps_all_fields z kvs = maps_all_fields z kvs' :=
by
  intro kvs kvs' z k v M
  unfold maps_all_fields
  simp_all only [eq_iff_iff]
  apply Iff.intro
  case mp => intro a; simp[←a]; apply hfields_update_preserves_fields; apply M
  case mpr => intro a; simp[←a]; symm; apply hfields_update_preserves_fields; apply M


lemma triple_set_field_hrecord : ∀ kvs kvs' k (p:loc) v,
  hfields_update k v kvs = some kvs' →
  triple [lang| ⟨val_set_field k⟩ p v]
    (hrecord kvs p)
    (fun _ => hrecord kvs' p) :=
by
  introv M
  unfold hrecord
  xtriple
  xpull
  intros z Hz
  xapp (triple_set_field_hfields  _ _ _ _ _ M)
  xsimp
  simp[←(hfields_update_preserves_maps_all_fields _ _ _ _ _ M)]
  apply Hz




lemma xapp_get_field_lemma : ∀ H k p Q,
  (H ==> ∃ʰ kvs, (hrecord kvs p) ∗
     (match hfields_lookup k kvs with
     | none => ⌜False⌝
     | some v => qwand (fun r => ⌜r = v ⌝  ∗ hrecord kvs p) (protect Q))) →
     (H ==> wpgen_app [lang| ⟨val_get_field k⟩ p] Q):=
by
  intro H k p Q N
  xchange N
  intro kvs
  generalize h :(hfields_lookup k kvs) = X
  cases (X)
  case none => xpull; intro contra; simp at contra
  case some v =>
    xsimp
    apply triple_conseq_frame
    { apply triple_get_field_hrecord; apply h }
    { xsimp }
    { apply qwand_cancel }



lemma xapp_set_field_lemma : ∀ H k p v Q,
  (H ==> ∃ʰ kvs, (hrecord kvs p) ∗
     (match hfields_update k v kvs with
     | none => ⌜False⌝
     | some kvs' => qwand (fun _ => hrecord kvs' p) (protect Q))) →
     (H ==> wpgen_app [lang| ⟨val_set_field k⟩ p v] Q):=
by
  intro H k p v Q N
  xchange N
  intro kvs
  generalize h :(hfields_update k v kvs) = X
  cases (X)
  case none => xpull; intro contra; simp at contra
  case some kvs' =>
    xsimp
    apply triple_conseq_frame
    { apply triple_set_field_hrecord; apply h }
    { xsimp }
    { apply qwand_cancel }


lemma hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p ∗ ⌜p ≠ null⌝ :=
by
  intro p kvs
  simp[hrecord]
  simp[hheader]
  xsimp
  { assumption }
  { assumption }
  { intros; assumption }
