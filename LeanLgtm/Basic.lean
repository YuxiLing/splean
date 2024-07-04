import Ssreflect.Lang
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
  | evalbinop_ptr_add : forall p1 p2 n,
      (p2:ℤ) = n + (p1:loc) ->
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


/- ====================== Heap Predicates ====================== -/

namespace hprop_scope
open hprop_scope

/- The type of heap predicates is named [hprop]. -/

abbrev hprop := heap -> Prop

/- Entailment for heap predicates, written [H1 ==> H2]. This entailment
    is linear. -/

abbrev himpl (H1 H2 : hprop) : Prop :=
  forall h, H1 h -> H2 h

infixr:51 " ==> " => himpl

/- Entailment between postconditions, written [Q1 ===> Q2]. -/

def qimpl {A} (Q1 Q2 : A → hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v

infixr:51 " ===> " => qimpl

/- --------- Definitions of Heap predicates --------- -/

def hempty : hprop :=
  fun h => (h = ∅)

def hsingle (p : loc) (v : val) : hprop :=
  fun h => (h = Finmap.singleton p v)

def hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2,
    H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2

def hexists {A} (J : A → hprop) : hprop :=
  fun h => exists x, J x h

def hforall {A} (J : A → hprop) : hprop :=
  fun h => forall x, J x h

notation:max "emp" => hempty
-- notation:max "" => hempty

infixr:60 " ~~> " => hsingle

infixr:55 " ∗ " => hstar

/- This notation sucks (`h` prefix is not uniform across other notations)
   But I dunno know what would be a better one -/
section
open Lean.TSyntax.Compat
macro "h∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hexists xs b
macro "h∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hforall xs b
end

@[app_unexpander hexists] def unexpandHExists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∃ $xs:binderIdent*, $b) => `(h∃ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∃ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander hforall] def unexpandHForall : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => h∀ $xs:binderIdent*, $b) => `(h∀ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(h∀ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(h∀ ($x:ident : $t), $b)
  | _                                              => throw ()


-- notation3 "exists' " (...) ", " J r:(scoped J => hexists J) => r

/- not quite sure about these two notations:



 notation3 "forall' " (...) ", " J r:(scoped J => hexists J) => r -/

/- TODO: Translate notations for hexists and hforall:

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.-/


/- Derived operators -/

def hpure (P : Prop) : hprop :=
  hexists (fun (_ : P) => emp)

def htop : hprop :=
  hexists (fun (H : hprop) => H)

def hwand (H1 H2 : hprop) : hprop :=
  hexists (fun (H0 : hprop) => H0 ∗ hpure ((H1 ∗ H0) ==> H2))

def qwand {A} (Q1 Q2 : A → hprop) : hprop :=
  hforall (fun (x : A) => hwand (Q1 x) (Q2 x))

/- this a better notation as for me -/
notation:max "⌜" P "⌝" => hpure P

/- ⊤⊤ is very annoynig, let's just overwrite lean's ⊤ -/
notation (priority := high) "⊤" => htop

def qstar {A} (Q : A → hprop) (H : hprop) : A → hprop :=
  fun x => hstar (Q x) H

infixr:54 " ∗∗ " => qstar

infixr:53 " -∗ " => hwand

infix:53 " -∗∗ " => qwand


/- ============ Properties of Separation Logic Operators ============ -/

/- ------------ Properties of [himpl] and [qimpl] ------------ -/

lemma himpl_refl H : H ==> H :=
by sdone

lemma himpl_trans H2 H1 H3 :
  (H1 ==> H2) → (H2 ==> H3) → (H1 ==> H3) :=
by
  sby move=> h1h2 ?? /h1h2


lemma himpl_trans_r H2 H1 H3:
  H2 ==> H3 → H1 ==> H2 → H1 ==> H3 :=
by
  move=> /[swap]
  apply himpl_trans

lemma himpl_antisym H1 H2:
  (H1 ==> H2) → (H2 ==> H1) → (H1 = H2) :=
by
  move=> h1imp2 h2imp1
  apply funext ; move=> ? ; apply propext
  apply Iff.intro
  { sby srw (himpl) at h1imp2 }
  { sby srw (himpl) at h2imp1 }

lemma hprop_op_comm (op : hprop → hprop → hprop) :
  (forall H1 H2, op H1 H2 ==> op H2 H1) →
  (forall H1 H2, op H1 H2 = op H2 H1) :=
by
  move=> *
  apply himpl_antisym <;> aesop


/- ---------------- Properties of [hempty] ---------------- -/

lemma hempty_intro : emp ∅ :=
  by srw hempty

lemma hempty_inv h :
  emp h → h = ∅ :=
by sapply

/- ---------------- Properties of [hstar] ---------------- -/

lemma hstar_intro H1 H2 h1 h2 :
  H1 h1 →
  H2 h2 →
  Finmap.Disjoint h1 h2 →
  (H1 ∗ H2) (h1 ∪ h2) :=
by
  sby move=> *

lemma hstar_inv H1 H2 h:
  (H1 ∗ H2) h →
  exists h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2 :=
by
   sapply

lemma hstar_comm H1 H2 :
  H1 ∗ H2 = H2 ∗ H1 :=
by
  apply hprop_op_comm
  move=> > ? /hstar_inv ![>??]
  move=> /[dup] /Finmap.Disjoint.symm ??
  sby srw Finmap.union_comm_of_disjoint


syntax "sdo" num tactic : tactic

partial def elabSDo (n : Nat) (tac : Lean.Elab.Tactic.TacticM Unit) : Lean.Elab.Tactic.TacticM Unit :=
  if n == 0 then do
    return ()
  else do
    tryGoal tac
    allGoal $ elabSDo (n - 1) tac

elab_rules : tactic
  | `(tactic| sdo $n $t) => do
    elabSDo n.getNat (elabTactic t)

lemma hstar_assoc H1 H2 H3 :
  (H1 ∗ H2) ∗ H3 = H1 ∗ (H2 ∗ H3) :=
by
  apply himpl_antisym=> h
  { scase! => h12 h3 ![h1 h2] ?? ? -> ?
    move=> /Finmap.disjoint_union_left[??] ->
    exists h1, h2 ∪ h3
    sdo 3 apply And.intro=> //
    { sby srw Finmap.disjoint_union_right }
    sby srw Finmap.union_assoc }
  { move=> ![h1 ?? [h2 [h3 ![??? h23eq]]] /h23eq
      /(Finmap.disjoint_union_right h1 h2 h3) [??] /h23eq hU]
    exists (h1 ∪ h2), h3
    sdo 3 apply And.intro=>//
    apply (Iff.mpr (Finmap.disjoint_union_left h1 h2 h3))=> //
    srw (hU) ; apply Eq.symm ; apply Finmap.union_assoc }

lemma hstar_hempty_l H :
  emp ∗ H = H :=
by
  apply himpl_antisym
  { sby move=> ? ![?? /hempty_inv]}
  move=> h ?
  exists ∅, h
  repeat' (constructor=>//)
  apply (Finmap.disjoint_empty h)

lemma hstar_hempty_r H :
  H ∗ emp = H :=
by
  srw (hstar_comm)
  apply hstar_hempty_l

lemma hstar_hexists A (J : A → hprop) H :
  (hexists J) ∗ H = hexists (fun x => (J x) ∗ H) :=
by
  apply himpl_antisym
  { sby move=> ? ![?? []] }
  sby move=> ? [? ![]]

lemma hstar_hforall A (J : A → hprop) H :
  (hforall J) ∗ H ==> hforall (J ∗∗ H) :=
by
  move=> ? [h1 ![h2 /hforall] * ?]
  sby exists h1, h2

lemma himpl_frame_l H1 H1' H2 :
  H1 ==> H1' →
  (H1 ∗ H2) ==> (H1' ∗ H2) :=
by
  srw himpl=> ?? ![ h1 h2 *]
  sby exists h1, h2

lemma himpl_frame_r H1 H2 H2' :
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1 ∗ H2') :=
by
  srw himpl=> ?? ![h1 h2 *]
  sby exists h1, h2

lemma himpl_frame_lr H1 H1' H2 H2' :
  H1 ==> H1' →
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1' ∗ H2') :=
by
  srw !himpl => ??? ![h1 h2 *]
  sby exists h1, h2

lemma himpl_hstar_trans_l H1 H2 H3 H4 :
  H1 ==> H2 →
  H2 ∗ H3 ==> H4 →
  H1 ∗ H3 ==> H4 :=
by
  srw !himpl => ? hStar23 ? ![h1 h3 *]
  apply hStar23
  sby exists h1, h3

lemma himpl_hstar_trans_r H1 H2 H3 H4 :
  H1 ==> H2 →
  H3 ∗ H2 ==> H4 →
  H3 ∗ H1 ==> H4 :=
by
  srw !himpl => ? hStar32 ? ![h3 h1 *]
  apply hStar32
  sby exists h3, h1


/- --------------- Properties of [hpure] --------------- -/

lemma hpure_intro P :
  P → ⌜P⌝  ∅ :=
by sdone

lemma hpure_inv P h :
  ⌜P⌝ h →
  P ∧ h = ∅ :=
by
  sby move=> []

lemma hstar_hpure_l P H h :
  (⌜P⌝ ∗ H) h = (P ∧ H h) :=
by
  srw hpure hstar_hexists hstar_hempty_l
  sby move=> ! ⟨|⟩ []

lemma hstar_hpure_r P H h :
  (H ∗ ⌜P⌝) h = (H h ∧ P) :=
by
  sby srw hstar_comm hstar_hpure_l

lemma himpl_hstar_hpure_r P H H' :
   P →
   (H ==> H') →
   H ==> ⌜P⌝ ∗ H' :=
by
  srw !himpl => *
  sby srw hstar_hpure_l

lemma hpure_inv_hempty P h :
  ⌜P⌝ h →
  P ∧ emp h :=
by
  sby srw -hstar_hpure_l hstar_hempty_r

lemma hpure_intro_hempty P h :
  emp h → P → ⌜P⌝ h :=
by
  sby move=> *

lemma himpl_hempty_hpure P :
  P → emp ==> ⌜P⌝ :=
by
  sby move=> ???

lemma himpl_hstar_hpure_l P H H' :
  (P → H ==> H') →
  (⌜P⌝ ∗ H) ==> H' :=
by
  srw himpl=> * ?
  sby srw hstar_hpure_l

lemma hempty_eq_hpure_true :
  emp = ⌜True⌝ :=
by
  apply himpl_antisym
  { move=> * ; sby apply hpure_intro_hempty }
  sby move=> ? []

lemma hfalse_hstar_any H :
  ⌜False⌝ ∗ H = ⌜False⌝ :=
by
  apply himpl_antisym
  { move=> ? ; sby srw hstar_hpure_l }
  move=> ? []
  sby srw hstar_hpure_l


/- ----------------- Properties of [hexists] ----------------- -/

lemma hexists_intro A (x : A) (J : A → hprop) h :
  J x h → (hexists J) h :=
by sdone

lemma hexists_inv A (J : A → hprop) h :
  (hexists J) h → exists x, J x h :=
by
  sby srw hexists

lemma himpl_hexists_l A H (J : A → hprop) :
  (forall x, J x ==> H) → (hexists J) ==> H :=
by
  srw [0](himpl)=> hJx ? [?]
  sby apply hJx

lemma himpl_hexists_r A (x : A) H (J : A → hprop) :
  (H ==> J x) →
  H ==> (hexists J) :=
by
  srw himpl=> * ??
  sby exists x

lemma himpl_hexists A (J1 J2 : A → hprop) :
  J1 ===> J2 →
  hexists J1 ==> hexists J2 :=
by
  srw qimpl=> hJs
  sby apply himpl_hexists_l=> ?? /hJs


/- ------------------- Properties of [hforall] ------------------- -/

lemma hforall_intro A (J : A → hprop) h :
  (forall x, J x h) → (hforall J) h :=
by sdone

lemma hforall_inv A (J : A → hprop) h :
  (hforall J) h → forall x, J x h :=
by
  sby srw hforall

lemma himpl_hforall_r A (J : A → hprop) H :
  (forall x, H ==> J x) →
  H ==> (hforall J) :=
by
  sby srw [0]himpl=> * ?

lemma himpl_hforall_l A (x : A) (J : A → hprop) H :
  (J x ==> H) →
  (hforall J) ==> H :=
by
  srw himpl=> ??
  sby srw hforall

lemma hforall_specialize A (x : A) (J : A → hprop) :
  (hforall J) ==> (J x) :=
by
  move=> ? ; sapply

lemma himpl_hforall A (J1 J2 : A → hprop) :
  J1 ===> J2 →
  hforall J1 ==> hforall J2 :=
by
  srw qimpl=> hQimp
  apply himpl_hforall_r=> ?
  apply himpl_hforall_l
  move: hQimp ; sapply


/- -------------------- Properties of [hwand] -------------------- -/

lemma hwand_equiv H0 H1 H2 :
  (H0 ==> H1 -∗ H2) ↔ (H1 ∗ H0 ==> H2) :=
by
  srw hwand ; apply Iff.intro
  { srw hstar_comm=> ?
    apply himpl_hstar_trans_l=>//
    srw hstar_hexists
    apply himpl_hexists_l=> ?
    srw [2](hstar_comm) (hstar_assoc) [2](hstar_comm)
    sby apply himpl_hstar_hpure_l }
  move=> ?
  apply himpl_hexists_r
  rw [<-hstar_hempty_r H0]
  apply himpl_frame_r ; sby apply himpl_hempty_hpure

lemma himpl_hwand_r H1 H2 H3 :
  H2 ∗ H1 ==> H3 →
  H1 ==> (H2 -∗ H3) :=
by
  sby srw hwand_equiv

lemma himpl_hwand_r_inv H1 H2 H3 :
  H1 ==> (H2 -∗ H3) →
  H2 ∗ H1 ==> H3 :=
by
  sby srw -hwand_equiv

lemma hwand_cancel H1 H2 :
  H1 ∗ (H1 -∗ H2) ==> H2 :=
by
  sby apply himpl_hwand_r_inv=> ?

lemma himpl_hempty_hwand_same H :
  emp ==> (H -∗ H) :=
by
  apply himpl_hwand_r
  sby srw hstar_hempty_r=> h

lemma hwand_hempty_l H :
  (emp -∗ H) = H :=
by
  apply himpl_antisym
  { rw [<- hstar_hempty_l (emp -∗ H)]
    apply hwand_cancel }
  apply himpl_hwand_r
  sby srw hstar_hempty_l=> ?

lemma hwand_hpure_l P H :
  P → (⌜P⌝ -∗ H) = H :=
by
  move=> ? ; apply himpl_antisym
  { apply himpl_trans
    apply (himpl_hstar_hpure_r P (⌜P⌝ -∗ H) (⌜P⌝ -∗ H))=>//
    apply himpl_refl
    apply hwand_cancel }
  srw hwand_equiv
  sby apply himpl_hstar_hpure_l=> ??

lemma hwand_curry H1 H2 H3 :
  (H1 ∗ H2) -∗ H3 ==> H1 -∗ (H2 -∗ H3) :=
by
  sdo 2 apply himpl_hwand_r;
  srw -hstar_assoc [0]hstar_comm
  apply hwand_cancel

lemma hwand_uncurry H1 H2 H3 :
  H1 -∗ (H2 -∗ H3) ==> (H1 ∗ H2) -∗ H3 :=
by
  srw hwand_equiv [2]hstar_comm hstar_assoc
  apply himpl_hstar_trans_r
  sdo 2 apply hwand_cancel;

lemma hwand_curry_eq H1 H2 H3 :
  (H1 ∗ H2) -∗ H3 = H1 -∗ (H2 -∗ H3) :=
by
  apply himpl_antisym
  { apply hwand_curry }
  apply hwand_uncurry

lemma hwand_inv h1 h2 H1 H2 :
  (H1 -∗ H2) h2 →
  H1 h1 →
  Finmap.Disjoint h1 h2 →
  H2 (h1 ∪ h2) :=
by
  move=> [? ![hW1 ?? [/himpl h1W hW2emp] ? /hW2emp /Finmap.union_empty hU *]]
  apply h1W ; exists h1, hW1
  sby srw hU


/- ----------------- Properties of [qwand] ----------------- -/

lemma qwand_equiv H A (Q1 Q2 : A → hprop) :
  H ==> (Q1 -∗∗ Q2) ↔ (Q1 ∗∗ H) ===> Q2 :=
by
  srw qwand ; apply Iff.intro
  { move=> ? x
    srw qstar hstar_comm
    apply (himpl_hstar_trans_l H (hforall fun x' ↦ Q1 x' -∗ Q2 x'))=>//
    apply (himpl_trans (hforall fun x0 ↦ ((Q1 x0 -∗ Q2 x0) ∗ Q1 x)))
    apply hstar_hforall ; apply himpl_hforall_l
    rw [hstar_comm] ; apply hwand_cancel }
  srw qimpl qstar => ?
  apply himpl_hforall_r => ?
  sby srw hwand_equiv=> ?

lemma qwand_cancel A (Q1 Q2 : A → hprop) :
  Q1 ∗∗ (Q1 -∗∗ Q2) ===> Q2 :=
by
  sby srw -qwand_equiv=> ?

lemma himpl_qwand_r A (Q1 Q2 : A → hprop) H :
  Q1 ∗∗ H ===> Q2 →
  H ==> (Q1 -∗∗ Q2) :=
by
  sby srw qwand_equiv

lemma qwand_specialize A (x : A) (Q1 Q2 : A → hprop) :
  (Q1 -∗∗ Q2) ==> (Q1 x -∗ Q2 x) :=
by
  sby apply (himpl_hforall_l A x)=> ?


/- --------------------- Properties of [htop] --------------------- -/

lemma htop_intro h :
  ⊤ h :=
by sdone

lemma himpl_htop_r H :
  H ==> ⊤ :=
by sdone

lemma htop_eq :
  ⊤ = h∃ H, H :=
by
  srw htop

lemma hstar_htop_htop :
  ⊤ ∗ ⊤ = ⊤ :=
by
  apply himpl_antisym
  { apply himpl_htop_r }
  srw -[1](hstar_hempty_r ⊤)
  apply himpl_frame_r ; apply himpl_htop_r


/- -------------------- Properties of [hsingle] -------------------- -/

lemma hsingle_intro p v :
  (p ~~> v) (Finmap.singleton p v) :=
by sdone

lemma hsingl_inv p v h :
  (p ~~> v) h →
  h = Finmap.singleton p v :=
by sapply

lemma disjoint_single_same_inv {α : Type u} {β : α → Type v}
  (p : α) (v1 v2 : β p) :
  Finmap.Disjoint (Finmap.singleton p v1) (Finmap.singleton p v2) →
  False :=
by
  sby srw Finmap.Disjoint Not => ?


lemma hstar_hsingle_same_loc p v1 v2 :
  (p ~~> v1) ∗ (p ~~> v2) ==> ⌜False⌝ :=
by
  move=> ? ![??]
  srw [0]hsingle => hh1 hh2 /hh1 /hh2 hDisj ?
  srw (hpure) (hexists) /==
  apply (disjoint_single_same_inv p v1 v2 hDisj)


/- -------- Definitions and Properties of [haffine] and [hgc] -------- -/

def haffine (_ : hprop) :=
  True

lemma haffine_hany : forall H,
  haffine H :=
by sdone

lemma haffine_hempty : haffine emp := haffine_hany emp

def hgc := htop -- Equivalent to [exists H, /[haffine H] ∗ H]

notation "/GC" => hgc

lemma haffine_hgc : haffine /GC := haffine_hany /GC

lemma himpl_hgc_r : forall H,
  haffine H →
  H ==> /GC :=
by
  sby move=> * ?

lemma hstar_hgc_hgc : /GC ∗ /GC = /GC := hstar_htop_htop


/- ------------------- Instantiate [xsimpl] ------------------- -/


/- ------------------ Properties of [haffine] ------------------ -/

lemma haffine_hpure P :
  haffine ⌜P⌝ :=
by
  apply haffine_hany

lemma haffine_hstar H1 H2 :
  haffine H1 → haffine H2 → haffine (H1 ∗ H2) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hexists A (J : A → hprop) :
  (forall x, haffine (J x)) →
  haffine (hexists J) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hforall A {_ : Inhabited A} (J : A → hprop) :
  (forall x, haffine (J x)) →
  haffine (hforall J) :=
by
  move=> * ; apply haffine_hany

lemma haffine_hastar_hpure (P : Prop) H :
  (P → haffine H) →
  haffine (⌜P⌝ ∗ H) :=
by
  move=> * ; apply haffine_hany


/- ------------- Definition and properties of [placeholder] ------------- -/

def hind : hprop :=
  hexists (fun b => if b then emp else ⊤)

notation:max "⊤⊤" => hind

lemma hind_any h : ⊤⊤ h :=
by
  sby exists false

lemma hind_hstar_hempty :
  ⊤⊤ ∗ emp ==> ⊤⊤ :=
by
  move=> *
  sby apply hind_any

/- TODO: Add more properties -/

/- ================= Separation Logic Reasoning Rules ================= -/

/- -------------- Definition of Separation Logic Triples -------------- -/

abbrev triple (t : trm) (H : hprop) (Q : val → hprop) : Prop :=
  forall s, H s → eval s t Q

notation "funloc" p "↦" H =>
  fun (r : val) ↦ hexists (fun p ↦ ⌜r = val_loc p⌝) ∗ H


/- ---------------- Structural Properties of [eval] ---------------- -/

section evalProp

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
  srw (qimpl) (himpl)=> ?
  elim: heval ; move=> * ; constructor=>//
  { sby constructor }
  { sby apply eval.eval_app_arg2 }
  { sby apply eval.eval_app_fun }
  { sby apply eval.eval_app_fix }
  { apply eval.eval_seq =>//
    move=> * ; aesop  }
  { sby constructor }
  { apply eval.eval_unop=>//
    sby srw (purepostin) at * }
  { apply eval.eval_binop=>//
    sby srw (purepostin) at * }
  { sby apply eval.eval_ref }
  { sby apply eval.eval_get }
  { sby apply eval.eval_set }
  sby apply eval.eval_free

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
  eval (h1 ∪ h2) t (Q ∗∗ (fun h ↦ h = h2)) :=
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
    srw qstar Finmap.insert_union ; apply hstar_intro=>//
    sby apply disjoint_insert_l }
  move=> * ; apply eval.eval_free=>//
  srw remove_disjoint_union_l ; apply hstar_intro=>//
  sby apply disjoint_remove_l

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

lemma triple_frame t H Q H' :
  triple t H Q →
  triple t (H ∗ H') (Q ∗∗ H') :=
by
  move=> /triple hEval
  srw triple=>? ![?? hs ? hDisj hU] ; srw hU
  apply eval_conseq
  { apply (eval_frame _ _ _ _ (hEval _ hs) hDisj) =>// }
  { sorry }
