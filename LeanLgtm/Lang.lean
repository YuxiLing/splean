-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import LeanLgtm.Util


open Classical

/- =========================== Language Syntax =========================== -/

inductive prim where
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_neg : prim
  | val_opp : prim
  | val_eq : prim
  | val_add : prim
  | val_neq : prim
  | val_sub : prim
  | val_mul : prim
  | val_div : prim
  | val_mod : prim
  | val_rand : prim
  | val_le : prim
  | val_lt : prim
  | val_ge : prim
  | val_gt : prim
  | val_ptr_add : prim

abbrev loc := Nat
abbrev var := String

def null : loc := 0

mutual
  inductive val : Type where
    | val_unit : val
    | val_bool : Bool → val
    | val_int : Int → val
    | val_loc : loc → val
    | val_prim : prim → val
    | val_fun : var -> trm -> val
    | val_fix : var -> var -> trm -> val
    | val_uninit : val
    | val_error : val
    | val_alloc : val
    -- | val_array_make : val
    -- | val_array_length : val
    -- | val_array_get : val
    -- | val_array_set : val

  inductive trm : Type where
    | trm_val : val -> trm
    | trm_var : var -> trm
    | trm_fun : var -> trm -> trm
    | trm_fix : var -> var -> trm -> trm
    | trm_app : trm -> trm -> trm
    | trm_seq : trm -> trm -> trm
    | trm_let : var -> trm -> trm -> trm
    | trm_if : trm -> trm -> trm -> trm
end

/- States and heaps are represented as finite maps -/
abbrev state := Finmap (λ _ : loc ↦ val)
abbrev heap := state

section
/- ============================= Notations ============================= -/

/- val and term are inhabited -/
instance : Inhabited val where
  default := val.val_unit

instance : Inhabited trm where
  default := trm.trm_val (val.val_unit)

/- Coercions -/
instance : Coe Bool val where
  coe b := val.val_bool b

instance : Coe Int val where
  coe z := val.val_int z

/- Help Lean to treat Nat as val -/
instance : OfNat val n where
  ofNat := val.val_int n

instance : Coe loc val where
  coe l := val.val_loc l

instance : Coe prim val where
  coe x := val.val_prim x

instance : Coe val trm where
  coe v := trm.trm_val v

instance : Coe var trm where
  coe x := trm.trm_var x

instance : CoeFun trm (fun _ => trm -> trm) where
  coe x := trm.trm_app x

/- ================== Terms, Values and Substitutions ================== -/
open trm

abbrev trm_is_val : trm → Prop
  | trm_val _ => true
  | _         => false

/- Capture-avoiding substitution -/
def subst (y : var) (v' : val) (t : trm) : trm :=
  -- let aux x := subst y v' x
  let if_y_eq x t1 t2 := if x = y then t1 else t2
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val v') t
  | trm_fun x t1 => trm_fun x (if_y_eq x t1 (subst y v' t1))
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (subst y v' t1)))
  | trm_app t1 t2 => trm_app (subst y v' t1) (subst y v' t2)
  | trm_seq t1 t2 => trm_seq (subst y v' t1) (subst y v' t2)
  | trm_let x t1 t2 => trm_let x (subst y v' t1) (if_y_eq x t2 (subst y v' t2))
  | trm_if t0 t1 t2 => trm_if (subst y v' t0) (subst y v' t1) (subst y v' t2)

noncomputable def is_true (P : Prop) : Bool :=
  if P then true else false


/- ======================= Small-Step Semantics ======================= -/
open val
open prim

/- Function for reading a memory location (to unwrap the option) -/
def read_state (p : loc) (h : state) :=
  match Finmap.lookup p h with
  | some v => v
  | none   => default

inductive step : state → trm → state → trm → Prop where

  -- Context Rules
  | step_seq_ctx : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_seq t1 t2) s2 (trm_seq t1' t2)
  | step_let_ctx : forall s1 s2 x t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)
  | step_app_arg_1 : forall s1 s2 t1 t1' t2,
      step s1 t1 s2 t1' →
      step s1 (trm_app t1 t2) s2 (trm_app t1' t2)
  | step_app_arg2 : forall s1 s2 v1 t2 t2',
      step s1 t2 s2 t2' →
      step s1 (trm_app v1 t2) s2 (trm_app v1 t2')

  -- Reduction
  | step_fun : forall s x t1,
      step s (trm_fun x t1) s (val_fun x t1)
  | step_fix : forall s f x t1,
      step s (trm_fix f x t1) s (val_fix f x t1)
  | step_app_fun : forall s v1 v2 x t1,
      v1 = val_fun x t1 →
      v2 = trm_val v2' →
      step s (trm_app v1 v2) s (subst x v2' t1)
  | step_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 →
      v2 = trm_val v2' →
      step s (trm_app v1 v2) s (subst x v2' (subst f v1 t1))
  | step_if : forall s b t1 t2,
      step s (trm_if (val_bool b) t1 t2) s (if b then t1 else t2)
  | step_seq : forall s t2 v1,
      step s (trm_seq v1 t2) s t2
  | step_let : forall s x t2 v1,
      v1 = trm_val v1' →
      step s (trm_let x v1 t2) s (subst x v1' t2)

  -- Unary Operations
  | step_neg : forall s b,
      step s (trm_app val_neg (val_bool b)) s (val_bool (¬ b))
  | step_opp : forall s n,
      step s (trm_app val_opp (val_int n)) s (val_int (- n))
  | step_rand : forall s n n1,
      0 <= n1 ∧ n1 < n →
      step s (trm_app val_rand (val_int n)) s (val_int n1)

  -- Binary Operations
  | step_eq : forall s v1 v2,
      step s (trm_app (trm_app val_eq v1) v2) s (val_bool (is_true (v1 = v2)))
  | step_neq : forall s v1 v2,
      step s (trm_app (trm_app val_neq v1) v2) s (val_bool (is_true (v1 ≠ v2)))
  | step_add : forall s n1 n2,
      step s (trm_app (trm_app val_add (val_int n1)) (val_int n2)) s
        (val_int (n1 + n2))
  | step_sub : forall s n1 n2,
      step s (trm_app (trm_app val_sub (val_int n1)) (val_int n2)) s
        (val_int (n1 - n2))
  | step_mul : forall s n1 n2,
      step s (trm_app (trm_app val_mul (val_int n1)) (val_int n2)) s
        (val_int (n1 * n2))
  | step_div : forall s n1 n2,
      n2 ≠ 0 →
      step s (trm_app (trm_app val_div (val_int n1)) (val_int n2)) s
        (n1 / n2)
  | step_mod : forall s n1 n2,
      n2 ≠ 0 →
      step s (trm_app (trm_app val_mod (val_int n1)) (val_int n2)) s
        (n1 % n2)
  | step_le : forall s n1 n2,
      step s (trm_app (trm_app val_le (val_int n1)) (val_int n2)) s
        (val_bool (n1 <= n2))
  | step_lt : forall s n1 n2,
      step s (trm_app (trm_app val_lt (val_int n1)) (val_int n2)) s
        (val_bool (n1 < n2))
  | step_ge : forall s n1 n2,
      step s (trm_app (trm_app val_ge (val_int n1)) (val_int n2)) s
        (val_bool (n1 >= n2))
  | step_gt : forall s n1 n2,
      step s (trm_app (trm_app val_gt (val_int n1)) (val_int n2)) s
        (val_bool (n1 > n2))
  | step_ptr_add : forall s p1 p2 n,
      (p2:ℤ) = (p1:loc) + n →
      step s (trm_app (trm_app val_ptr_add (val_loc p1)) (val_int n)) s
        (val_loc (Int.toNat p2))

  -- Heap Opeartions
  | step_ref : forall s v p,
      ¬ p ∈ s →
      v = trm_val v' →
      step s (trm_app val_ref v) (Finmap.insert p v' s) (val_loc p)
  | step_get : forall s p,
      p ∈ s →
      step s (trm_app val_get (val_loc p)) s (read_state p s)
  | step_set : forall s p v,
      p ∈ s ->
      v = trm_val v' →
      step s (trm_app (trm_app val_set (val_loc p)) v)
        (Finmap.insert p v' s) val_unit
  | step_free : forall s p,
      p ∈ s →
      step s (trm_app val_free (val_loc p)) (Finmap.erase p s) val_unit

/- Multi-step relation -/
inductive steps : state → trm → state → trm → Prop :=
  | steps_refl : forall s t,
      steps s t s t
  | steps_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 →
      steps s2 t2 s3 t3 →
      steps s1 t1 s3 t3

lemma steps_of_step s1 s2 t1 t2 :
  step s1 t1 s2 t2 → steps s1 t1 s2 t2 :=
by
  sby move=> ?; apply steps.steps_step

lemma steps_trans s1 s2 s3 t1 t2 t3 :
  steps s1 t1 s2 t2 →
  steps s2 t2 s3 t3 →
  steps s1 t1 s3 t3 := by sby elim

/- Predicate [reducible s t] for asserting that [(s, t)] can step -/
def reducible (s : state) (t : trm) : Prop :=
  exists s' t', step s t s' t'

/- The configuration [(s, t)] is not stuck, i.e. [notstuck s t] if either
   t is a value or [(s, t)] can step -/
def notstuck (s : state) (t : trm) : Prop :=
  trm_is_val t \/ reducible s t


/- ========== Big-step Semantics for Primitive Operations ========== -/

/- Big-step relation for unary operators -/
inductive evalunop : prim → val → (val → Prop) → Prop where
  | evalunop_neg : forall b1,
      evalunop val_neg (val_bool b1) (fun v => v = val_bool (¬ b1))
  | evalunop_opp : forall n1,
      evalunop val_opp (val_int n1) (fun v => v = val_int (- n1))
  | evalunop_rand : forall n,
      n > 0 →
      evalunop val_rand (val_int n)
        (fun r => exists n1, r = val_int n1 ∧ 0 <= n1 ∧ n1 < n)

/- Big-step relation for binary operators -/
inductive evalbinop : val → val → val → (val->Prop) → Prop where
  | evalbinop_eq : forall v1 v2,
      evalbinop val_eq v1 v2 (fun v => v = val_bool (is_true (v1 = v2)))
  | evalbinop_neq : forall v1 v2,
      evalbinop val_neq v1 v2 (fun v => v = val_bool (is_true (v1 ≠ v2)))
  | evalbinop_add : forall n1 n2,
      evalbinop val_add (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 + n2))
  | evalbinop_sub : forall n1 n2,
      evalbinop val_sub (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 - n2))
  | evalbinop_mul : forall n1 n2,
      evalbinop val_mul (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 * n2))
  | evalbinop_div : forall n1 n2,
      ¬(n2 = 0) →
      evalbinop val_div (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 / n2))
  | evalbinop_mod : forall n1 n2,
      ¬(n2 = 0) →
      evalbinop val_mod (val_int n1) (val_int n2)
        (fun v => v = val_int (n1 % n2))
  | evalbinop_le : forall n1 n2,
      evalbinop val_le (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 <= n2))
  | evalbinop_lt : forall n1 n2,
      evalbinop val_lt (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 < n2))
  | evalbinop_ge : forall n1 n2,
      evalbinop val_ge (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 >= n2))
  | evalbinop_gt : forall n1 n2,
      evalbinop val_gt (val_int n1) (val_int n2)
        (fun v => v = val_bool (n1 > n2))

  -- Not really sure what's going on in the last rule here since
  -- in the original CFML code, p2 doesn't have to be a valid pointer (it has
  -- type int and could be negative), so not sure if this is semantically
  -- equivalent to what was here before.
  | evalbinop_ptr_add : forall (p1 : loc) (p2 : Int) n,
      p2 = p1 + n ->
      evalbinop val_ptr_add (val_loc p1) (val_int n)
        (fun v => v = val_loc (Int.toNat p2))


/- ========================= Big-step Semantics ========================= -/

section eval

/- Predicate for converting predicates [P : val → Prop] into postconditions
   of type [val → state → Prop] that hold in state s -/
def purepost (s : state) (P : val → Prop) : val → state → Prop :=
  fun v s' => P v ∧ s' = s

def purepostin (s : state) (P : val → Prop) (Q : val → state → Prop) : Prop :=
  -- Equivalent to [purepost S P ===> Q]
  forall v, P v → Q v s

variable (Q : val → state → Prop)


/- To define the evaluation rule for arrays, it is useful to first define
   the notion of consecutive locations -/

def conseq {B : Type} (vs : List B) (l : Nat) : Finmap (fun _ : Nat ↦ B) :=
  match vs with
  | [] => ∅
  | v :: vs' => (Finmap.singleton l v) ∪ (conseq vs' (l + 1))

lemma conseq_nil B (l : Nat) :
  conseq ([] : List B) l = ∅ := by
  sdone

lemma conseq_cons B (l : Nat) (v : B) (vs : List B) :
  conseq (v :: vs) l = (Finmap.singleton l v) ∪ (conseq vs (l + 1)) := by
  sdone

lemma disjoint_single_conseq B l l' L (v : B) :
  (l < l') ∨ (l ≥ l' + L.length) →
  Finmap.Disjoint (Finmap.singleton l v) (conseq L l') := by
  induction L generalizing l' with
  | nil          =>
      srw conseq_nil Finmap.Disjoint.symm_iff=> ?
      apply Finmap.disjoint_empty
  | cons h t ih =>
      srw conseq_cons Finmap.disjoint_union_right /= => [] ? ⟨|⟩
      { sby move=> ? ; srw Not ?Finmap.mem_singleton }
      { sby apply ih }
      { move=> ? ; srw Not ?Finmap.mem_singleton ; omega }
      { apply ih ; omega }

/- For initializing a list with value v -/
def make_list {A} (n : Nat) (v : A) : List A :=
  match n with
  | 0      => []
  | n' + 1 => v :: make_list n' v


/- Big-step relation -/
inductive eval : state → trm → (val → state → Prop) -> Prop where
  | eval_val : forall s v Q,
      Q v s ->
      eval s (trm_val v) Q
  | eval_fun : forall s x t1 Q,
      Q (val_fun x t1) s ->
      eval s (trm_fun x t1) Q
  | eval_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      eval s (trm_fix f x t1) Q
  | eval_app_arg1 : forall s1 t1 t2 Q1 Q,
      ¬ trm_is_val t1 ->
      eval s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
      eval s1 (trm_app t1 t2) Q
  | eval_app_arg2 : forall s1 v1 t2 Q1 Q,
      ¬ trm_is_val t2 ->
      eval s1 t2 Q1 ->
      (forall v2 s2, Q1 v2 s2 -> eval s2 (trm_app v1 v2) Q) ->
      eval s1 (trm_app v1 t2) Q
  | eval_app_fun : forall s1 v1 v2 x t1 Q,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) Q ->
      eval s1 (trm_app v1 v2) Q
  | eval_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      eval s (subst x v2 (subst f v1 t1)) Q ->
      eval s (trm_app v1 v2) Q
  | eval_seq : forall Q1 s t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 t2 Q) ->
      eval s (trm_seq t1 t2) Q
  | eval_let : forall Q1 s x t1 t2 Q,
      eval s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> eval s2 (subst x v1 t2) Q) ->
      eval s (trm_let x t1 t2) Q
  | eval_if : forall s (b : Bool) t1 t2 Q,
      eval s (if b then t1 else t2) Q ->
      eval s (trm_if (val_bool b) t1 t2) Q
  | eval_unop : forall op s v1 P Q,
      evalunop op v1 P ->
      purepostin s P Q ->
      eval s (trm_app op v1) Q
  | eval_binop : forall op s v1 v2 P Q,
      evalbinop op v1 v2 P ->
      purepostin s P Q ->
      eval s (trm_app (trm_app op v1) v2) Q
  | eval_ref : forall s v Q,
      v = trm_val v' ->
      (forall p, ¬ p ∈ s ->
          Q (val_loc p) (Finmap.insert p v' s)) ->
      eval s (trm_app val_ref v) Q
  | eval_get : forall s p Q,
      p ∈ s ->
      Q (read_state p s) s ->
      eval s (trm_app val_get (val_loc p)) Q
  | eval_set : forall s p v Q,
      v = trm_val v' ->
      p ∈ s ->
      Q val_unit (Finmap.insert p v' s) ->
      eval s (trm_app (trm_app val_set (val_loc p)) v) Q
  | eval_free : forall s p Q,
      p ∈ s ->
      Q val_unit (Finmap.erase p s) ->
      eval s (trm_app val_free (val_loc p)) Q
  | eval_alloc : forall (n : Int) (sa : state) Q,
      n ≥ 0 →
      ( forall (p : loc) (sb : state),
          sb = conseq (make_list n.natAbs val_uninit) p →
          p ≠ null →
          Finmap.Disjoint sa sb →
          Q (val_loc p) (sb ∪ sa) ) →
      eval sa (trm_app val_alloc n) Q

/- Not sure if the rules eval_ref and eval_set are correct. I had to add the
   condition [v = trm_val v'] to get the definition to type-check. However, this
   assertion says that the term v is a value but really shouldn't this be
   that v big-steps to a value? Not sure what the best way to do this is.
   Perhaps by doing something like the seq rule where there is some
   intermediate condition Q' for first evaluating v and then composing that
   with the memory allocation. -/

/- Rule for values to instantiate postconditions -/

lemma eval_val_minimal s v :
  eval s (trm_val v) (fun v' s' => (v' = v) /\ (s' = s)) :=
  by sby apply eval.eval_val


/- Special rules to avoid unecessary use of [evalbinop] and [evalunop] -/

lemma eval_add  s n1 n2 Q :
  Q (val_int (n1 + n2)) s →
  eval s (trm_app (trm_app val_add (val_int n1)) (val_int n2)) Q :=
by
  move=> ?
  apply eval.eval_binop
  { apply evalbinop.evalbinop_add }
  sdone

lemma eval_div s n1 n2 Q :
  n2 ≠ 0 ->
  Q (val_int (n1 / n2)) s ->
  eval s (trm_app (trm_app val_div (val_int n1)) (val_int n2)) Q :=
by
  move=> *
  apply eval.eval_binop
  { apply evalbinop.evalbinop_div=>// }
  sdone

lemma eval_rand s (n : ℤ) Q :
  n > 0 ->
  (forall n1, 0 <= n1 ∧ n1 < n -> Q n1 s) ->
  eval s (trm_app val_rand (val_int n)) Q :=
by
  move=> *
  apply eval.eval_unop
  { apply evalunop.evalunop_rand=>// }
  sby move=> ? []


/- Derived rules for reasoning about applications that don't require checking
   if terms are already values -/

lemma eval_app_arg1' s1 t1 t2 Q1 Q :
  eval s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> eval s2 (trm_app v1 t2) Q) ->
  eval s1 (trm_app t1 t2) Q :=
by
  move=> hevals1 hevals2
  scase: [(trm_is_val t1)]=> hVal
  { sby apply eval.eval_app_arg1 }
  sby scase: t1=> // ? []

/- TODO: optimise (similar to ↑) -/
lemma eval_app_arg2' : forall s1 v1 t2 Q1 Q,
  eval s1 t2 Q1 ->
  (forall v2 s2, eval s2 (trm_app v1 v2) Q) ->
  eval s1 (trm_app v1 t2) Q :=
by
  move=> s1 v1 t2 Q1 Q hevals1 hevals2
  scase: [(trm_is_val t2)]=> hVal
  { apply eval.eval_app_arg2=>// }
  sby scase: t2


/- [eval_like t1 t2] asserts that [t2] evaluates like [t1], i.e.,
    this relation holds whenever [t2] reduces in small-step to [t1]. -/
def eval_like (t1 t2:trm) : Prop :=
  forall s Q, eval s t1 Q -> eval s t2 Q

end eval

/- ================================================================= -/
/-* ** Notation for Concrete Terms -/

def trm_apps (f:trm) (ts:List trm) : trm :=
  match ts with
  | [] => f
  | ti::ts' => trm_apps (trm_app f ti) ts'

def trm_funs (xs:List var) (t:trm) : trm :=
  match xs with
  | [] => t
  | x1::xs' => trm_fun x1 (trm_funs xs' t)

def val_funs (xs:List var) (t:trm) : val :=
  match xs with
  | [] => panic! "function with zero argumets!"
  | x1::xs' => val_fun x1 (trm_funs xs' t)

def trm_fixs (f:var) (xs:List var) (t:trm) : trm :=
  match xs with
  | [] => t
  | x1::xs' => trm_fix f x1 (trm_funs xs' t)

def val_fixs (f:var) (xs:List var) (t:trm) : val :=
  match xs with
  | .nil => val_uninit
  | x1::xs' => val_fix f x1 (trm_funs xs' t)

end

open trm val prim

declare_syntax_cat lang
declare_syntax_cat bop
declare_syntax_cat uop

-- #check let x := (); let y := (); y

syntax ident : lang
syntax num : lang
syntax:20 lang ";" ppDedent(ppLine lang) : lang
syntax:25 lang lang:30 : lang
syntax "if " lang "then " lang "end " : lang
syntax ppIndent("if " lang " then") ppSpace lang ppDedent(ppSpace) ppRealFill("else " lang) : lang
syntax "let" ident " := " lang " in" ppDedent(ppLine lang) : lang
-- TODO: I suspect it should be  `withPosition(lang ";") ppDedent(ppLine lang) : lang`, but Lean parser crashes. Report a bug.
syntax "fun" ident+ " => " lang : lang
syntax "fix" ident ident+ " => " lang : lang
syntax "fun_ " ident* " => " lang : lang
syntax "fix_ " ident ident* " => " lang : lang
syntax "()" : lang
syntax uop lang:30 : lang
syntax lang:30 bop lang:30 : lang
syntax "(" lang ")" : lang
syntax "{" term "}" : lang

syntax " := " : bop
syntax " + " : bop
syntax " - " : bop
syntax " * " : bop
syntax " / " : bop
syntax " < " : bop
syntax " > " : bop
syntax " <= " : bop
syntax " >= " : bop
syntax " = " : bop
syntax " != " : bop
syntax " mod " : bop
syntax " ++ " : bop

syntax "!" : uop
syntax "-" : uop
syntax "ref" : uop
syntax "free" : uop
syntax "not" : uop

syntax "[lang|\n" lang "]" : term
syntax "[bop|\n" bop "]" : term
syntax "[uop|\n" uop "]" : term


local notation "%" x => (Lean.quote (toString (Lean.Syntax.getId x)))


macro_rules
  | `([lang| ()])                       => `(trm_val (val_unit))
  | `([lang| $n:num])                   => `(trm_val (val_int $n))
  | `([lang| $t1 $t2])                  => `(trm_app [lang| $t1] [lang| $t2])
  | `([lang| if $t1 then $t2 else $t3]) => `(trm_if [lang| $t1] [lang| $t2] [lang| $t3])
  | `([lang| if $t1 then $t2 end])      => `(trm_if [lang| $t1] [lang| $t2] (trm_val val_unit))
  | `([lang| let $x := $t1:lang in $t2:lang])     =>
    `(trm_let $(%x) [lang| $t1] [lang| $t2])
  | `([lang| $t1 ; $t2])                => `(trm_seq [lang| $t1] [lang| $t2])
  | `([lang| fun_ $xs* => $t])             => do
    let xs <- xs.mapM fun x => `(term| $(%x))
    `(trm_funs [ $xs,* ] [lang| $t])
  | `([lang| fun $xs* => $t])             => do
    let xs <- xs.mapM fun x => `(term| $(%x))
    `(val_funs [ $xs,* ] [lang| $t])
  | `([lang| fix_ $f $xs* => $t])    => do
      let xs <- xs.mapM fun x => `(term| $(%x))
      `(trm_fixs $(%f) [ $xs,* ] [lang| $t])
  | `([lang| fix $f $xs* => $t])    => do
      let xs <- xs.mapM fun x => `(term| $(%x))
      `(val_fixs $(%f) [ $xs,* ] [lang| $t])
  | `([lang| ref $t])                   => `(trm_val (val_prim val_ref) [lang| $t])
  | `([lang| free $t])                  => `(trm_val (val_prim val_free) [lang| $t])
  | `([lang| not $t])                   => `(trm_val (val_prim val_not) [lang| $t])
  | `([lang| !$t])                      => `(trm_val val_get [lang| $t])
  | `([lang| $t1 := $t2])               => `(trm_val val_set [lang| $t1] [lang| $t2])
  | `([lang| $t1 + $t2])                => `(trm_val val_add [lang| $t1] [lang| $t2])
  | `([lang| $t1 * $t2])                => `(trm_val val_mul [lang| $t1] [lang| $t2])
  | `([lang| $t1 - $t2])                => `(trm_val val_sub [lang| $t1] [lang| $t2])
  | `([lang| $t1 / $t2])                => `(trm_val val_div [lang| $t1] [lang| $t2])
  | `([lang| $t1 < $t2])                => `(trm_val val_lt [lang| $t1] [lang| $t2])
  | `([lang| $t1 > $t2])                => `(trm_val val_gt [lang| $t1] [lang| $t2])
  | `([lang| $t1 <= $t2])               => `(trm_val val_le [lang| $t1] [lang| $t2])
  | `([lang| $t1 >= $t2])               => `(trm_val val_ge [lang| $t1] [lang| $t2])
  | `([lang| -$t])                      => `(trm_val val_opp [lang| $t])
  | `([lang| $t1 = $t2])                => `(trm_val val_eq [lang| $t1] [lang| $t2])
  | `([lang| $t1 != $t2])               => `(trm_val val_neq [lang| $t1] [lang| $t2])
  | `([lang| $t1 mod $t2])              => `(trm_val val_mod [lang| $t1] [lang| $t2])
  | `([lang| $t1 ++ $t2])               => `(trm_val val_ptr_add [lang| $t1] [lang| $t2])
  | `([lang| ($t)]) => `([lang| $t])
  | `([lang| {$t}]) => `(val_int $t)


open Lean Elab Term
elab_rules : term
  | `([lang| $x:ident]) => do
    try do
      (<- withoutErrToSorry <| elabTermAndSynthesize x none).ensureHasNoMVars
      elabTerm (<- `(trm_val $x)) none
    catch _ => do
      let x <- `(trm_var $(%x))
      elabTerm x none

@[app_unexpander val_unit] def unexpandUnitL : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([lang| ()])
  -- | _ => throw ( )

@[app_unexpander val_int] def unexpandInt : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num) => `($n:num)
  | `($(_) $n:ident) => `($n:ident)
  | `($(_) $n:term) => `({$n:term})
  | _ => throw ( )

@[app_unexpander val_loc] def unexpandLoc : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:ident) => `($n:ident)
  | _ => throw ( )

@[app_unexpander val_prim] def unexpandPrim : Lean.PrettyPrinter.Unexpander
  | `($(_) val_ref) => `([uop| ref])
  | `($(_) val_free) => `([uop| free])
  | `($(_) val_not) => `([uop| not])
  | `($(_) val_opp) => `([uop| -])
  | `($(_) val_get) => `([uop| !])
  | `($(_) val_add) => `([bop| +])
  | `($(_) val_mul) => `([bop| *])
  | `($(_) val_sub) => `([bop| -])
  | `($(_) val_div) => `([bop| /])
  | `($(_) val_lt) => `([bop| <])
  | `($(_) val_gt) => `([bop| >])
  | `($(_) val_le) => `([bop| <=])
  | `($(_) val_ge) => `([bop| >=])
  | `($(_) val_eq) => `([bop| =])
  | `($(_) val_neq) => `([bop| !=])
  | `($(_) val_mod) => `([bop| mod])
  | `($(_) val_set) => `([bop| :=])
  | `($(_) val_ptr_add) => `([bop| ++])
  | _ => throw ( )

@[app_unexpander trm_val] def unexpandVal : Lean.PrettyPrinter.Unexpander := fun x =>
  match x with
  | `($(_) $x:ident) =>
    match x with
    | `(val_unit) => `([lang| ()])
    | _ => `([lang| $x:ident])
  | `($(_) $x) =>
    match x with
    | `($n:num) => `([lang| $n:num])
    | `($n:ident) => `([lang| $n:ident])
    | `({$n:term}) => `([lang| {$n}])
    | `([lang| $_]) => return x
    | `([uop| $_]) => return x
    | `([bop| $_]) => return x
    | t => `([lang| {$t}])
  | _ => throw ( )

@[app_unexpander trm_app] def unexpandApp : Lean.PrettyPrinter.Unexpander := fun x => do
  match x with
  | `($(_) [uop|$uop] [lang| $t]) =>
    match uop with
    | `(uop| ref)  => `([lang| ref $t])
    | `(uop| free) => `([lang| free $t])
    | `(uop| not)  => `([lang| not $t])
    | `(uop| !)    => `([lang| !$t])
    | `(uop| -)    => `([lang| -$t])
    | _ => throw ( )
  | `($(_) $app [lang| $t2]) =>
    -- dbg_trace app
    match app with
    | `([bop| $bop].trm_app [lang| $t1]) =>
      match bop with
      | `(bop| :=) => `([lang| $t1 := $t2])
      | `(bop| +) => `([lang| $t1 + $t2])
      | `(bop| *) => `([lang| $t1 * $t2])
      | `(bop| -) => `([lang| $t1 - $t2])
      | `(bop| /) => `([lang| $t1 / $t2])
      | `(bop| <) => `([lang| $t1 < $t2])
      | `(bop| >) => `([lang| $t1 > $t2])
      | `(bop| <=) => `([lang| $t1 <= $t2])
      | `(bop| >=) => `([lang| $t1 >= $t2])
      | `(bop| =) => `([lang| $t1 = $t2])
      | `(bop| !=) => `([lang| $t1 != $t2])
      | `(bop| mod) => `([lang| $t1 mod $t2])
      | _ => throw ( )
    | `([lang| $t1]) => `([lang| $t1 $t2])
    | _ => throw ( )
  | `($(_) [bop| $bop] [lang| $t1]) => return x
  | _ => throw ( )

@[app_unexpander trm_var] def unexpandVar : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| $name:ident])
  | _ => throw ( )

@[app_unexpander trm_seq] def unexpandSeq : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $t1] [lang| $t2]) => `([lang| $t1 ; $t2])
  | _ => throw ( )

@[app_unexpander trm_let] def unexpandLet : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| $t1] [lang| $t2]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| let $name := $t1 in $t2])
  | _ => throw ( )

@[app_unexpander trm_if] def unexpandIf : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $t1] [lang| $t2] [lang| $t3]) => `([lang| if $t1 then $t2 else $t3])
  | _ => throw ( )

@[app_unexpander trm_fun] def unexpandTFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| fun $xs* => $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name $xs* => $t])
  | `($(_) $x:str [lang| $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name => $t])
  | _ => throw ( )

@[app_unexpander val_fun] def unexpandVFun : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:str [lang| fun $xs* => $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name $xs* => $t])
  | `($(_) $x:str [lang| $t]) =>
    let str := x.getString
    let name := Lean.mkIdent $ Lean.Name.mkSimple str
    `([lang| fun $name => $t])
  | _ => throw ( )

@[app_unexpander trm_fix] def unexpandTFix : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str $x:str [lang| fun $xs* => $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX $xs* => $t])
  | `($(_) $f:str $x:str [lang| $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX => $t])
  | _ => throw ( )

@[app_unexpander val_fix] def unexpandVFix : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str $x:str [lang| fun $xs* => $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX $xs* => $t])
  | `($(_) $f:str $x:str [lang| $t]) =>
    let f := f.getString
    let x := x.getString
    let nameF := Lean.mkIdent $ Lean.Name.mkSimple f
    let nameX := Lean.mkIdent $ Lean.Name.mkSimple x
    `([lang| fix $nameF $nameX => $t])
  | _ => throw ( )

-- @[app_unexpander trm_apps] def unexpandApps : Lean.PrettyPrinter.Unexpander
--   -- Unexpand function applications when arguments are program-variables
--   | `($(_) [lang| $f] [ $[[lang|$xs]],* ]) => `([lang| $f  $xs )])
--   -- | `($(_) $f:ident [ $[[lang|$xs]],* ]) => `([lang| $f:ident ( $xs,* )])
--   -- Unexpand function applications when arguments are meta-variables
--   | `($(_) $f:ident [ $xs:term,* ]) => do
--     -- hack to workaround the fact that elements of `xs` are identifiers with
--     -- explicit coercions: [val_loc p, val_int n, ....]
--     let x <- xs.getElems.mapM fun
--        | `($(_) $i:ident) => `(ident| $i:ident)
--        | _ => throw ( )
--     `([lang| $f:ident ( $[ $x:ident],* )])
--   | _ => throw ( )

@[app_unexpander trm_funs] def unexpandTFuns : Lean.PrettyPrinter.Unexpander
  | `($(_) [ $xs:str,* ] [lang| $f]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    `([lang| fun $xs* => $f])
  | _ => throw ( )

@[app_unexpander val_funs] def unexpandVFuns : Lean.PrettyPrinter.Unexpander := fun x =>
  match x with
  | `($(_) [ $xs:str,* ] [lang| $f]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    `([lang| fun $xs* => $f])
  | _ => throw ( )

@[app_unexpander trm_fixs] def unexpandTFixs : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str [ $xs:str,* ] [lang| $t]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    let f := Lean.mkIdent $ Lean.Name.mkSimple f.getString
    `([lang| fix $f $xs* => $t])
  | _ => throw ( )

@[app_unexpander val_fixs] def unexpandVFixs : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:str [ $xs:str,* ] [lang| $t]) =>
    let xs := xs.getElems.map (Lean.mkIdent $ Lean.Name.mkSimple ·.getString)
    let f := Lean.mkIdent $ Lean.Name.mkSimple f.getString
    `([lang| fix $f $xs* => $t])
  | _ => throw ( )


-- #check [lang| 1-1]

#check fun (p : loc)  => [lang|
  fix f y z =>
    if F y z
    then
      let y := {1 + 1}in
      let y := 1 + 1 in
      let z := !p in
      y + z
    else
      let y := 1 + 1 in
      let z := 1 in
      y + z]

#check [lang| x; let x := !x in let y:= () in x]
#check [lang|x y; z]
#check [lang|!x; y]
instance : HAdd ℤ ℕ val := ⟨fun x y => val_int (x + (y : Int))⟩
#check fun n : ℤ => (([lang| ()]).trm_seq (trm_val ((n + 1))))
#check [lang| 1 ++ 2]
