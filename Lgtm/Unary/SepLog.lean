-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp

open trm val prim

local instance : Coe val trm where
  coe v := trm.trm_val v

/- ================= Separation Logic Reasoning Rules ================= -/

/- -------------- Definition of Separation Logic Triples -------------- -/

abbrev triple (t : trm) (H : hProp) (Q : val → hProp) : Prop :=
  forall s, H s → eval s t Q

notation "funloc" p "↦" H =>
  fun (r : val) ↦ hexists (fun p ↦ ⌜r = val_loc p⌝ ∗ H)


/- ---------------- Structural Properties of [eval] ---------------- -/

section evalProp

set_option maxHeartbeats 250000
/- Is there a good way to automate this? The current problem is that
   [constructor] does not always infer the correct evaluation rule to use.
   Since many of the rules involve a function application, using [constructor]
   often incorrectly applys eval_app_arg1, so we must instead manually apply
   the correct rule -/
lemma eval_conseq s t Q1 Q2 :
  eval s t Q1 →
  Q1 ===> Q2 →
  eval s t Q2 :=
by
  move=> heval
  srw (qimpl) (himpl)=> Imp
  elim: heval ; move=> * ; constructor=>//
  { sby constructor }
  { sby apply eval.eval_app_arg2 }
  { sby apply eval.eval_app_fun }
  { sby apply eval.eval_app_fix }
  { apply eval.eval_seq =>//
    move=> * ; aesop  }
  { sby constructor=>// }
  { apply eval.eval_unop=>//
    sby srw (purepostin) at * }
  { apply eval.eval_binop=>//
    sby srw (purepostin) at * }
  { sby apply eval.eval_ref }
  { sby apply eval.eval_get }
  { sby apply eval.eval_set }
  apply eval.eval_free <;> try assumption
  case eval_free.a Imp x y =>
    apply Imp
    apply y
  sby apply eval.eval_alloc

/- Useful Lemmas about disjointness and state operations -/
lemma disjoint_update_not_r (h1 h2 : state) (x : loc) (v: val) :
  Finmap.Disjoint h1 h2 →
  x ∉ h2 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => ??
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma in_read_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → read_state x (h1 ∪ h2) = read_state x h1 :=
by
  move=> ?
  srw []read_state
  sby srw (Finmap.lookup_union_left)

lemma disjoint_insert_l (h1 h2 : state) (x : loc) (v : val) :
  Finmap.Disjoint h1 h2 →
  x ∈ h1 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => *
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma remove_disjoint_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → Finmap.Disjoint h1 h2 →
  Finmap.erase x (h1 ∪ h2) = Finmap.erase x h1 ∪ h2 :=
by
  srw Finmap.Disjoint => * ; apply Finmap.ext_lookup => y
  scase: [x = y]=> hEq
  { scase: [y ∈ Finmap.erase x h1]=> hErase
    { srw Finmap.lookup_union_right
      rw [Finmap.lookup_erase_ne]
      apply Finmap.lookup_union_right
      srw Finmap.mem_erase at hErase=>//
      srw Not at * => * //
      sby srw Not }
    srw Finmap.lookup_union_left
    sby sdo 2 rw [Finmap.lookup_erase_ne] }
  srw -hEq
  srw Finmap.lookup_union_right=>//
  srw Finmap.lookup_erase
  apply Eq.symm
  sby srw Finmap.lookup_eq_none

lemma disjoint_remove_l (h1 h2 : state) (x : loc) :
  Finmap.Disjoint h1 h2 →
  Finmap.Disjoint (Finmap.erase x h1) h2 :=
by
  srw Finmap.Disjoint=> ??
  sby srw Finmap.mem_erase


lemma eval_frame (h1 h2 : state) t Q :
  eval h1 t Q →
  Finmap.Disjoint h1 h2 →
  eval (h1 ∪ h2) t (Q ∗ (fun h ↦ h = h2)) :=
by
  move=> heval
  elim: heval h2
  { sby move=> * }
  { sby move=> * }
  { sby move=> * }
  { move=> ???????? ih1 ?? /ih1 ? ; constructor=>//
    sby move=> ?? ![] }
  { move=> ???????? ih1 ?? /ih1 ? ; apply eval.eval_app_arg2=>//
    sby move=> ?? ![] }
  { sby move=> * ; apply eval.eval_app_fun }
  { sby move=> * ; apply eval.eval_app_fix }
  { move=> ??????? ih1 ih2 ? /ih1 ? ; apply eval.eval_seq=>//
    move=> ? s2 ![??? hQ2 *] ; subst s2 hQ2
    sby apply ih2 }
  { move=> ???????? ih1 ih2 ? /ih1 ? ; apply eval.eval_let=>//
    move=> ?? ![??? hQ2 ? hU] ; subst hU hQ2
    sby apply ih2}
  { sby move=> * }
  { move=> * ; apply eval.eval_unop=>//
    srw purepostin at * => ??
    sby apply hstar_intro }
  { move=> * ; apply eval.eval_binop=>//
    srw purepostin at * => ??
    sby apply hstar_intro }
  { move=> * ; apply eval.eval_ref=>//
    move=> ? ; srw (Not) (Finmap.insert_union) => ?
    apply hstar_intro=>//
    sby apply disjoint_update_not_r }
  { move=> * ; apply eval.eval_get=>//
    srw in_read_union_l ; sby apply hstar_intro }
  { move=> * ; apply eval.eval_set=>//
    srw qstarE Finmap.insert_union ; apply hstar_intro=>//
    sby apply disjoint_insert_l }
  { move=> * ; apply eval.eval_free=>//
    srw remove_disjoint_union_l ; apply hstar_intro=>//
    sby apply disjoint_remove_l }
  { move=> >? ih * ; apply eval.eval_alloc=>//
    move=> > /ih h /h hQ1 /[dup] /Finmap.disjoint_union_left [] /hQ1 *
    srw qstarE -Finmap.union_assoc
    apply hstar_intro=>//
    srw Finmap.disjoint_union_left at *
    sby srw Finmap.Disjoint.symm_iff }
  all_goals move=> //

end evalProp


/- --------------------- Structural Rules --------------------- -/

/- For proofs below, [sorry] takes the place of [xsimp] -/

/- Consequence and Frame Rule -/

lemma triple_conseq t H' Q' H Q :
  triple t H' Q' →
  H ==> H'→
  Q' ===> Q →
  triple t H Q :=
by
  move=> /triple *
  srw triple => ??
  sby apply (eval_conseq _ _ Q' _)

lemma triple_frame t H (Q : val -> hProp) H' :
  triple t H Q →
  triple t (H ∗ H') (Q ∗ H') :=
by
  move=> /triple hEval
  srw triple=>? ![?? hs ? hDisj hU] ; srw hU
  apply eval_conseq
  { apply (eval_frame _ _ _ _ (hEval _ hs) hDisj) =>// }
  { move=> ?
    sby srw ?qstarE ; xsimp }


/- Extraction Rules -/

lemma triple_hpure t P H Q :
  (P → triple t H Q) →
  triple t (⌜P⌝ ∗ H) Q :=
by
  move=> ?
  srw triple=> ? ![?? [? /hempty_inv hEmp] ?? hU]
  sby srw hU hEmp Finmap.empty_union

lemma triple_hexists t A (J : A → hProp) Q :
  (forall x, triple t (J x) Q) →
  triple t (hexists J) Q :=
by
  sby srw []triple => hJ ? [] ? /hJ

lemma triple_hforall t A (x : A) (J : A → hProp) Q:
  triple t (J x) Q →
  triple t (hforall J) Q :=
by
  move=> /triple_conseq ; sapply => ?
  sapply ; sdone

lemma triple_hwand_hpure_l t (P : Prop) H Q :
  P →
  triple t H Q →
  triple t (⌜P⌝ -∗ H) Q :=
by
  move=> ? /triple_conseq ; sapply
  rw [hwand_hpure_l] <;> sdone
  sby move=> ??

/- A useful corollary of [triple_hpure] -/
lemma triple_hpure' t (P : Prop) Q :
  (P → triple t emp Q) →
  triple t ⌜P⌝ Q :=
by
  move=> /triple_hpure
  sby srw hstar_hempty_r

/- Heap -naming rule -/
lemma triple_named_heap t H Q :
  (forall h, H h → triple t (fun h' ↦ h' = h) Q) →
  triple t H Q :=
by
  sby move=> hH ? /hH

/- Combined and ramified rules -/

lemma triple_conseq_frame H2 H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ H2 →
  Q1 ∗ H2 ===> Q →
  triple t H Q :=
by
  move=> /triple_frame hFra /triple_conseq hCons /hCons
  sapply ; apply hFra

lemma triple_ramified_frame H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ (Q1 -∗ Q) →
  triple t H Q :=
by
  move=> ??;
  apply triple_conseq_frame=>//
  sby srw -qwand_equiv=> ?


/- ---------------------- Rules for Terms ---------------------- -/

lemma triple_eval_like t1 t2 H Q :
  eval_like t1 t2 →
  triple t1 H Q →
  triple t2 H Q :=
by
  srw eval_like=> hLike ? ??
  sby apply hLike

lemma triple_val v H Q :
  H ==> Q v →
  triple (trm_val v) H Q :=
by
  move=> ? ??
  sby apply eval.eval_val

lemma triple_val_minimal v :
  triple (trm_val v) emp (fun r ↦ ⌜r = v⌝) :=
by
  apply triple_val
  xsimp

lemma triple_fun x t1 H Q :
  H ==> Q (val_fun x t1) →
  triple (trm_fun x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fun

lemma triple_fix f x t1 H Q :
  H ==> Q (val_fix f x t1) →
  triple (trm_fix f x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fix

lemma triple_seq t1 t2 H Q H1 :
  triple t1 H (fun _ ↦ H1) →
  triple t2 H1 Q →
  triple (trm_seq t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_seq
  { sby apply hH }
  sdone

lemma triple_let x t1 t2 Q1 H Q :
  triple t1 H Q1 →
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) →
  triple (trm_let x t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_let
  { sby apply hH }
  sdone

lemma triple_let_val x v1 t2 H Q :
  triple (subst x v1 t2) H Q →
  triple (trm_let x v1 t2) H Q :=
by
  move=> ?
  apply triple_let _ _ _ (fun v ↦ ⌜v = v1⌝ ∗ H)
  { apply triple_val ; xsimp }
  move=> ?
  sby apply triple_hpure

lemma triple_if (b : Bool) t1 t2 H Q :
  triple (if b then t1 else t2) H Q →
  triple (trm_if b t1 t2) H Q :=
by
  move=> ? ??
  sby apply eval.eval_if

lemma triple_app_fun x v1 v2 t1 H Q :
  v1 = val_fun x t1 →
  triple (subst x v2 t1) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fun

lemma triple_app_fun_direct x v2 t1 H Q :
  triple (subst x v2 t1) H Q →
  triple (trm_app (val_fun x t1) v2) H Q :=
by
  move=> ?
  sby apply triple_app_fun

lemma triple_app_fix v1 v2 f x t1 H Q :
  v1 = val_fix f x t1 →
  triple (subst x v2 (subst f v1 t1)) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fix

lemma triple_app_fix_direct v2 f x t1 H Q :
  f ≠ x →
  triple (subst x v2 (subst f (val_fix f x t1) t1)) H Q →
  triple (trm_app (val_fix f x t1) v2) H Q :=
by
  move=> * ??
  sby apply triple_app_fix


/- Rules for Heap-Manipulating Primitive Operations -/

lemma read_state_single p v :
  read_state p (Finmap.singleton p v) = v :=
by
  srw read_state Finmap.lookup_singleton_eq

lemma triple_ref (v : val) :
  triple (trm_app val_ref v)
    emp
    (fun r ↦ h∃ p, ⌜r = val_loc p⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_ref=>// p ?
  apply (hexists_intro _ p)
  sby srw hstar_hpure_l

lemma triple_get v (p : loc) :
  triple (trm_app val_get p)
    (p ~~> v)
    (fun r ↦ ⌜r = v⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_get=>//
  srw hstar_hpure_l => ⟨|⟩ //
  apply read_state_single

lemma triple_set w p (v : val) :
  triple (trm_app val_set (val_loc p) v)
    (p ~~> w)
    (fun r ↦ ⌜r = val_unit⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_set=>//
  sby srw Finmap.insert_singleton_eq hstar_hpure_l

lemma triple_free' p v :
  triple (trm_app val_free (val_loc p))
    (p ~~> v)
    (fun r ↦ ⌜r = val_unit⌝) :=
by
  move=> ? []
  apply eval.eval_free=>//
  srw hpure hexists hempty
  exists rfl
  apply Finmap.ext_lookup => ?
  sby srw Finmap.lookup_empty Finmap.lookup_eq_none Finmap.mem_erase

lemma triple_free p v:
  triple (trm_app val_free (val_loc p))
    (p ~~> v)
    (fun _ ↦ emp) :=
by
  apply (triple_conseq _ _ _ _ _ (triple_free' p v))
  { sdone }
  xsimp ; xsimp

/- Rules for Other Primitive Operations -/

lemma triple_unop op v1 (P : val → Prop) :
  evalunop op v1 P →
  triple (trm_app op v1) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_unop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_binop op v1 v2 (P : val → Prop) :
  evalbinop op v1 v2 P →
  triple (trm_app op v1 v2) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_binop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_add n1 n2 :
  triple (trm_app val_add (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 + n2)⌝) :=
by
  sby apply triple_binop

lemma triple_div n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_div (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 / n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_rand n :
  n > 0 →
  triple (trm_app val_rand (val_int n))
    emp
    (fun r ↦ ⌜exists n1, r = val_int n1 ∧ 0 <= n1 ∧ n1 < n⌝) :=
by
  move=> ?
  sby apply triple_unop

lemma triple_neg (b1 : Bool) :
  triple (trm_app val_neg b1)
    emp
    (fun r ↦ ⌜r = val_bool (¬b1)⌝) :=
by
  sby apply triple_unop

lemma triple_opp n1 :
  triple (trm_app val_opp (val_int n1))
    emp
    (fun r ↦ ⌜r = val_int (-n1)⌝) :=
by
  sby apply triple_unop

lemma triple_eq v1 v2 :
  triple (trm_app val_eq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 = v2)⌝) :=
by
  sby apply triple_binop

lemma triple_neq v1 v2 :
  triple (trm_app val_neq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 ≠ v2)⌝) :=
by
  sby apply triple_binop

lemma triple_sub n1 n2 :
  triple (trm_app val_sub (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 - n2)⌝):=
by
  sby apply triple_binop

lemma triple_mul n1 n2 :
  triple (trm_app val_mul (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 * n2)⌝):=
by
  sby apply triple_binop

lemma triple_mod n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_mod (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 % n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_le n1 n2 :
  triple (trm_app val_le (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 <= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_lt n1 n2 :
  triple (trm_app val_lt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 < n2)⌝) :=
by
  sby apply triple_binop

lemma triple_ge n1 n2 :
  triple (trm_app val_ge (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 >= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_gt n1 n2 :
  triple (trm_app val_gt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 > n2)⌝) :=
by
  sby apply triple_binop

lemma abs_nonneg n :
  n ≥ 0 → Int.natAbs n = n :=
by
  move=> ?
  sby elim: n

lemma triple_ptr_add (p : loc) (n : ℤ) :
  p + n >= 0 →
  triple (trm_app val_ptr_add p n)
    emp
    (fun r ↦ ⌜r = val_loc ((p + n).natAbs)⌝) :=
by
  move=> ?
  apply triple_binop
  apply evalbinop.evalbinop_ptr_add
  sby srw abs_nonneg

lemma triple_ptr_add_nat p (f : ℕ) :
  triple (trm_app val_ptr_add (val_loc p) (val_int (Int.ofNat f)))
    emp
    (fun r ↦ ⌜r = p + f⌝) :=
by
  apply triple_conseq _ _ _ _ _ (triple_ptr_add p f _)=>// ? /=
  sby xsimp

/- --------------------- Strongest Post Condition --------------------- -/

abbrev sP h t :=fun v => h∀ (Q : val -> hProp), ⌜eval h t Q⌝ -∗ Q v

open Classical
lemma hpure_intr :
  (P -> H s) -> (⌜P⌝ -∗ H) s := by
  move=> ?
  scase: [P]=> p
  { exists ⊤, s, ∅; repeat' constructor=> //
    { xsimp=>// }
    sorry }
  sorry

lemma hforall_impl (J₁ J₂ : α -> hProp) :
  (forall x, J₁ x ==> J₂ x) ->
  hforall J₁ ==> hforall J₂ := by
  move=> ? h /[swap]  x/(_ x)//

lemma sP_strongest :
  eval h t Q -> sP h t ===> Q := by
  move=> ev v; unfold sP;
  apply himpl_hforall_l _ Q
  srw hwand_hpure_l=> //

set_option maxHeartbeats 400000 in
lemma sP_post :
  eval h t Q -> eval h t (sP h t) := by
  elim=> >
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ? evv ev' ih ih'; apply eval.eval_app_arg1=> //
    move=> > ?; apply eval_conseq=> //
    apply ih'
    { apply sP_strongest; apply evv=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> //
    { move=> ?? /sP_strongest himp; sapply
      sby apply himp }
    { scase=> // [] // ?? []// }
    move=> >? []// }
  { move=> ? ev₁; intro ih ih' sp
    apply eval.eval_app_arg2=> // > sp'
    apply eval_conseq=> //
    apply sp
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ??/sP_strongest himp; sapply=> //
    sby apply himp }
  { move=> -> ? ih; apply eval.eval_app_fun=> //
    apply eval_conseq=> //
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> -> ? ih; apply eval.eval_app_fix=> //
    apply eval_conseq=> //
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> ev₁ _ sp ih₂; constructor; apply sp
    move=> > ?
    apply eval_conseq=> //; apply ih₂
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ? ev₁; sapply
    apply sP_strongest; apply ev₁=> // }
  { move=> ev₁ _ sp ih₂; constructor; apply sp
    move=> > ?
    apply eval_conseq=> //; apply ih₂
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ? ev₁; sapply
    apply sP_strongest; apply ev₁=> // }
  { move=> ev sp; constructor
    apply eval_conseq=> // v
    dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> eop pp; apply eval.eval_unop=> // ? ??
    apply hpure_intr=> []//??; sapply
    scase: eop
    { move=> ? [] //== }
    { move=> ? [] // }
    move=> ? [] // }
  { move=> eop pp; apply eval.eval_binop=> // ? ??
    apply hpure_intr=> []//?
    { move=> ? [] // [] // }
    move=> eop'; sapply; scase: eop
    any_goals (try scase: eop'=> //)
    any_goals (try move=> ?? [] //)
    move=> ???->? []// }
  { move=> ->?; apply eval.eval_ref=> // ???
    apply hpure_intr=> []// }
  { move=> ??; apply eval.eval_get=> // ?
    apply hpure_intr=> []// }
  { move=> ->??; apply eval.eval_set=> // ?
    apply hpure_intr=> []// ?? []// }
  { move=> ??; apply eval.eval_free=> // ?
    apply hpure_intr=> []// }
  { move=> ??; apply eval.eval_alloc=> // *?
    apply hpure_intr=> []// }
  { move=> ev₁ ev₂; constructor
    apply eval_conseq=> // v
    dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    sby scase: ev }
  move=> ev₁ ev₂; constructor
  apply eval_conseq=> // v
  dsimp [sP]; apply himpl_hforall=> Q/=
  xsimp=> ev; srw hwand_hpure_l=> //
  sby scase: ev

lemma finite_state (s : state) :
  ∃ p, p ∉ s := by sorry

lemma finite_state' n (s : state) :
  ∃ p, p ≠ null ∧
    Finmap.Disjoint s (conseq (make_list n val_uninit) p) := by sorry

lemma eval_sat :
  eval h t Q -> ∃ h v, Q h v := by
  elim=> // >
  { move=> ??? ![>?]; sapply=> // }
  { move=> ??? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> //
    move=> ? pp; sdo 2 econstructor; apply pp=> //}
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> //
    any_goals move=> ? pp; (sdo 2 econstructor); apply pp=> // }
  { move=> ?; scase: (finite_state s)=> p /[swap]/[apply]// }
  sby move=> ?; scase: (finite_state' n.natAbs sa)=> p ? /(_ p) H
