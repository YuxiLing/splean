import Ssreflect.Lang
import Mathlib.Data.Finmap


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

-- def isTrue (p : Prop) : Bool :=
--   if p then true else false

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
  move=>//

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

infixr:52 " ~~> " => hsingle

infixr:53 " ∗ " => hstar

/- This notation sucks (`h` prefix is not uniform across other notations)
   But I dunno know what would be a better one -/
section
open Lean.TSyntax.Compat
macro "h∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hexists xs b
macro "h∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``hforall xs b
end


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

infixr:53 " ∗∗ " => qstar

infixr:54 " -∗ " => hwand

infix:54 " -∗∗ " => qwand


/- ============ Properties of Separation Logic Operators ============ -/

/- ------------ Properties of [himpl] and [qimpl] ------------ -/

lemma himpl_refl H : H ==> H :=
by sdone

/-
  H : C -> A -> B
  ------
  A -> .....
 -/

lemma himpl_trans H2 H1 H3 :
  (H1 ==> H2) → (H2 ==> H3) → (H1 ==> H3) :=
by
  sby move=> h1h2 ?? /h1h2


lemma himpl_trans_r : forall H2 H1 H3,
  H2 ==> H3 → H1 ==> H2 → H1 ==> H3 :=
by
  move=> H2 H1 H3 /[swap]
  apply himpl_trans

lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) → (H2 ==> H1) → (H1 = H2) :=
by
  move=> H1 H2 h1imp2 h2imp1
  apply funext ; move=> h ; apply propext
  apply Iff.intro
  { srw (himpl) at h1imp2=>// }
  { srw (himpl) at h2imp1=>// }

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
  move=> hH1 hH2 hDisj=> //

lemma hstar_inv : forall H1 H2 h,
  (H1 ∗ H2) h →
  exists h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2 :=
by
  move=> H1 H2 h ; sapply

lemma hstar_comm H1 H2 :
  H1 ∗ H2 = H2 ∗ H1 :=
by
  apply hprop_op_comm
  -- move => H1 H2 h /hstar_inv ![h1 h2 ??]
  -- move=> /[dup] ? /Finmap.Disjoint.symm ? ->
  -- exists h2, h1
  -- sby srw Finmap.union_comm_of_disjoint
  -- -- move=> ![h1 h2 hH1 hH2 hDisj hU]
  -- have hDisjSymm : Finmap.Disjoint h2 h1 := Finmap.Disjoint.symm h1 h2 hDisj
  -- have hUSymm : h = h2 ∪ h1 :=
  --   by srw (Finmap.union_comm_of_disjoint hDisj) at hU=>//
  -- exists h2, h1
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
  { move=> ![h1 h23 hH1 [h2 [h3 ![hH2 hH3 hDisj23 h23eq]]] hDisj hU]
    srw (h23eq) at * ; exists (h1 ∪ h2), h3
    apply (Iff.mp (Finmap.disjoint_union_right h1 h2 h3)) in hDisj=>//
    move=> hDisj
    constructor=>//
    { apply hstar_intro=>// }
    constructor=>//
    constructor
    apply (Iff.mpr (Finmap.disjoint_union_left h1 h2 h3))=>//
    srw (hU) ; apply Eq.symm ; apply Finmap.union_assoc }

lemma hstar_hempty_l : forall H,
  emp ∗ H = H :=
by
  move=>H
  apply himpl_antisym
  { move=> h ![h1 h2 hEmpty hH ? hU]
    apply hempty_inv in hEmpty =>// }
  { move=> h hH
    exists ∅, h
    repeat' (constructor=>//)
    apply (Finmap.disjoint_empty h) }

lemma hstar_hempty_r : forall H,
  H ∗ emp = H :=
by
  move=> H
  srw (hstar_comm)
  apply hstar_hempty_l

lemma hstar_hexists : forall A (J : A → hprop) H,
  (hexists J) ∗ H = hexists (fun x => (J x) ∗ H) :=
by
  move=> A J H ; apply himpl_antisym
  { move=> h ![h1 h2 [x] hJ hH hDisj hU]
    exists x=>// }
  { move=> h [x ![h1 h2 hJ hH hDisj hU]]
    exists h1, h2 =>// }

lemma hstar_hforall : forall A (J : A → hprop) H,
  (hforall J) ∗ H ==> hforall (J ∗∗ H) :=
by
  move=> A J H h [h1 ![h2 hFAJ] hH hDisj hU x]
  srw (hforall) at hFAJ
  exists h1, h2=>//

lemma himpl_frame_l : forall H1 H1' H2,
  H1 ==> H1' →
  (H1 ∗ H2) ==> (H1' ∗ H2) :=
by
  move=> H1 H1' H2
  srw (himpl)=> hH1' h ![ h1 h2 hH1 hH2 hDisj hU]
  exists h1, h2 =>//

lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1 ∗ H2') :=
by
  move=> H1 H2 H2'
  srw (himpl)=> hH2' h ![h1 h2 hH1 hH2 hDisj hU]
  exists h1, h2 =>//

lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' →
  H2 ==> H2' →
  (H1 ∗ H2) ==> (H1' ∗ H2') :=
by
  move=> H1 H1' H2 H2'
  srw !(himpl) => hH1' hH2' h ![h1 h2 hH1 hH2 hDisj hU]
  exists h1, h2 =>//

lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 →
  H2 ∗ H3 ==> H4 →
  H1 ∗ H3 ==> H4 :=
by
  move=> H1 H2 H3 H4
  srw !himpl => hH12 hStar23 h ![h1 h3 hH1 hH3 hDisj hU]
  apply hStar23
  exists h1, h3 =>//

lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 →
  H3 ∗ H2 ==> H4 →
  H3 ∗ H1 ==> H4 :=
by
  move=> H1 H2 H3 H4
  srw !himpl => hH12 hStar32 h ![h3 h1 hH3 hH1 hDisj hU]
  apply hStar32
  exists h3, h1 =>//


/- --------------- Properties of [hpure] --------------- -/

lemma hpure_intro : forall P,
  P → ⌜P⌝  ∅ :=
by
  move=> P hP
  exists hP

lemma hpure_inv : forall P h,
  ⌜P⌝ h →
  P ∧ h = ∅ :=
by
  move=> P h []=>//

lemma hstar_hpure_l : forall P H h,
  (⌜P⌝ ∗ H) h = (P ∧ H h) :=
by
  move=> P H h
  apply propext
  srw (hpure) (hstar_hexists) (hstar_hempty_l)
  apply Iff.intro
  { move=> [hP] // }
  { move=> [] // }

lemma hstar_hpure_r : forall P H h,
  (H ∗ ⌜P⌝) h = (H h ∧ P) :=
by
  move=> P H h
  srw (hstar_comm) (hstar_hpure_l)=>//

lemma himpl_hstar_hpure_r : forall P H H',
   P →
   (H ==> H') →
   H ==> ⌜P⌝ ∗ H' :=
by
  move=> P H H' hP
  srw !(himpl) => hH1 h
  srw (hstar_hpure_l) =>//

lemma hpure_inv_hempty : forall P h,
  ⌜P⌝ h →
  P ∧ emp h :=
by
  move=> P H
  srw -(hstar_hpure_l) (hstar_hempty_r) =>//

lemma hpure_intro_hempty : forall P h,
  emp h → P → ⌜P⌝ h :=
by
  move=> P h=>//

lemma himpl_hempty_hpure : forall P,
  P → emp ==> ⌜P⌝ :=
by
  move=> P hP h
  move: hP=>//

lemma himpl_hstar_hpure_l : forall P H H',
  (P → H ==> H') →
  (⌜P⌝ ∗ H) ==> H' :=
by
  move=> P H H'
  srw (himpl)=> hPimp h
  srw (hstar_hpure_l)=>//

lemma hempty_eq_hpure_true :
  emp = ⌜True⌝ :=
by
  apply himpl_antisym
  { move=>h hEmp
    apply hpure_intro_hempty=>// }
  { move=> h hT
    apply hpure_inv_hempty in hT=>// }

lemma hfalse_hstar_any : forall H,
  ⌜False⌝ ∗ H = ⌜False⌝ :=
by
  move=> H ; apply himpl_antisym
  { move=> h
    srw (hstar_hpure_l)=>// }
  { move=> h hF
    srw (hstar_hpure_l)
    apply hpure_inv_hempty in hF=>// }

/- ----------------- Properties of [hexists] ----------------- -/

lemma hexists_intro : forall A (x : A) (J : A → hprop) h,
  J x h → (hexists J) h :=
by
  move=> A x J h =>//

lemma hexists_inv : forall A (J : A → hprop) h,
  (hexists J) h → exists x, J x h :=
by
  move=> A J h
  srw (hexists) ; sapply

lemma himpl_hexists_l : forall A H (J : A → hprop),
  (forall x, J x ==> H) → (hexists J) ==> H :=
by
  move=> A H J
  srw [0](himpl)=> hJx h [a]
  move: hJx ; sapply

lemma himpl_hexists_r : forall A (x : A) H (J : A → hprop),
  (H ==> J x) →
  H ==> (hexists J) :=
by
  move=> A x H J
  srw (himpl)=> hHimpJ h hH
  exists x=>//

lemma himpl_hexists : forall A (J1 J2 : A → hprop),
  J1 ===> J2 →
  hexists J1 ==> hexists J2 :=
by
  move=> A J1 J2
  srw (qimpl)=> hJs
  apply (himpl_hexists_l)=> x h hJ1
  apply hJs in hJ1=>//


/- ------------------- Properties of [hforall] ------------------- -/

lemma hforall_intro : forall A (J : A → hprop) h,
  (forall x, J x h) → (hforall J) h :=
by
  move=> A J h hJ=>//

lemma hforall_inv : forall A (J : A → hprop) h,
  (hforall J) h → forall x, J x h :=
by
  move=> A J h
  srw (hforall) ; sapply

lemma himpl_hforall_r : forall A (J : A → hprop) H,
  (forall x, H ==> J x) →
  H ==> (hforall J) :=
by
  move=> A J H
  srw [0](himpl)=> hJ h hH x =>//

lemma himpl_hforall_l : forall A (x : A) (J : A → hprop) H,
  (J x ==> H) →
  (hforall J) ==> H :=
by
  move=> A x J H
  srw (himpl)=> hImp h
  srw (hforall)=>//

lemma hforall_specialize : forall A (x : A) (J : A → hprop),
  (hforall J) ==> (J x) :=
by
  move=> A x J h
  srw (hforall) ; sapply

lemma himpl_hforall : forall A (J1 J2 : A → hprop),
  J1 ===> J2 →
  hforall J1 ==> hforall J2 :=
by
  move=> A J1 J2
  srw (qimpl)=> hQimp
  apply himpl_hforall_r=> x
  apply himpl_hforall_l
  move: hQimp ; sapply


/- -------------------- Properties of [hwand] -------------------- -/

lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 -∗ H2) ↔ (H1 ∗ H0 ==> H2) :=
by
  move=> H0 H1 H2 ; srw (hwand) ; apply Iff.intro
  { srw (hstar_comm)=> hEx
    apply (himpl_hstar_trans_l) ; apply hEx
    srw (hstar_hexists)
    apply himpl_hexists_l=> H'
    srw [2](hstar_comm) (hstar_assoc) [2](hstar_comm)
    apply himpl_hstar_hpure_l=>//  }
  { move=> h1star0imp2
    apply (himpl_hexists_r)
    rw [<-hstar_hempty_r H0]
    apply (himpl_frame_r) ; apply himpl_hempty_hpure=>// }

lemma himpl_hwand_r : forall H1 H2 H3,
  H2 ∗ H1 ==> H3 →
  H1 ==> (H2 -∗ H3) :=
by
  move=> H1 H2 H3
  srw (hwand_equiv); sapply

lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 -∗ H3) →
  H2 ∗ H1 ==> H3 :=
by
  move=> H1 H2 H3
  srw -(hwand_equiv); sapply

lemma hwand_cancel : forall H1 H2,
  H1 ∗ (H1 -∗ H2) ==> H2 :=
by
  move=> H1 H2
  apply himpl_hwand_r_inv=> h; sapply

lemma himpl_hempty_hwand_same : forall H,
  emp ==> (H -∗ H) :=
by
  move=> H
  apply himpl_hwand_r
  srw (hstar_hempty_r)=> h ; sapply

lemma hwand_hempty_l : forall H,
  (emp -∗ H) = H :=
by
  move=> H ; apply himpl_antisym
  { rw [<- hstar_hempty_l (emp -∗ H)]
    apply hwand_cancel }
  { apply himpl_hwand_r
    srw (hstar_hempty_l)=> h ; sapply }

lemma hwand_hpure_l : forall P H,
  P → (⌜P⌝ -∗ H) = H :=
by
  move=> P H hP ; apply himpl_antisym
  { apply himpl_trans
    apply (himpl_hstar_hpure_r P (⌜P⌝ -∗ H) (⌜P⌝ -∗ H))=>//
    apply himpl_refl
    apply hwand_cancel }
  { srw (hwand_equiv)
    apply himpl_hstar_hpure_l=> ? h ; sapply }

lemma hwand_curry : forall H1 H2 H3,
  (H1 ∗ H2) -∗ H3 ==> H1 -∗ (H2 -∗ H3) :=
by
  move=> H1 H2 H3
  apply himpl_hwand_r ; apply himpl_hwand_r
  srw -(hstar_assoc) [0](hstar_comm)
  apply hwand_cancel

lemma hwand_uncurry : forall H1 H2 H3,
  H1 -∗ (H2 -∗ H3) ==> (H1 ∗ H2) -∗ H3 :=
by
  move=> H1 H2 H3
  srw (hwand_equiv) [2](hstar_comm) (hstar_assoc)
  apply himpl_hstar_trans_r
  apply (hwand_cancel) ; apply (hwand_cancel)

lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 ∗ H2) -∗ H3 = H1 -∗ (H2 -∗ H3) :=
by
  move=> H1 H2 H3 ; apply himpl_antisym
  { apply hwand_curry }
  { apply hwand_uncurry }

lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 -∗ H2) h2 →
  H1 h1 →
  Finmap.Disjoint h1 h2 →
  H2 (h1 ∪ h2) :=
by
  move=> h1 h2 H1 H2 [HW hFun] hH1 hDisj
  apply hstar_inv in hFun=> ![hW1 hW2 hHW hWpure ? hU]
  apply hpure_inv in hWpure=> [h1W hW2emp]
  srw (himpl) at h1W ; srw (hW2emp) at hU
  apply h1W ; exists h1, hW1
  srw (Finmap.union_empty) at hU : hDisj
  srw (hU) //


/- ----------------- Properties of [qwand] ----------------- -/

lemma qwand_equiv : forall H A (Q1 Q2 : A → hprop),
  H ==> (Q1 -∗∗ Q2) ↔ (Q1 ∗∗ H) ===> Q2 :=
by
  move=> H A Q1 Q2 ; srw (qwand) ; apply Iff.intro
  { move=> hForall x /=
    srw (qstar) (hstar_comm)
    apply (himpl_hstar_trans_l H (hforall fun x' ↦ Q1 x' -∗ Q2 x'))=> //
    apply (himpl_trans (hforall fun x0 ↦ ((Q1 x0 -∗ Q2 x0) ∗ Q1 x)))
    apply (hstar_hforall) ; apply (himpl_hforall_l)
    rw [hstar_comm] ; apply hwand_cancel }
  { srw (qimpl) (qstar) => hQimp
    apply (himpl_hforall_r)=> x
    srw (hwand_equiv) // }

lemma qwand_cancel : forall A (Q1 Q2 : A → hprop),
  Q1 ∗∗ (Q1 -∗∗ Q2) ===> Q2 :=
by
  move=> A Q1 Q2
  srw -(qwand_equiv)=> v //

lemma himpl_qwand_r : forall A (Q1 Q2 : A → hprop) H,
  Q1 ∗∗ H ===> Q2 →
  H ==> (Q1 -∗∗ Q2) :=
by
  move=> A Q1 Q2 H
  srw (qwand_equiv) ; sapply

lemma qwand_specialize : forall A (x : A) (Q1 Q2 : A → hprop),
  (Q1 -∗∗ Q2) ==> (Q1 x -∗ Q2 x) :=
by
  move=> A x Q1 Q2
  apply (himpl_hforall_l A x)=> h ; sapply


/- --------------------- Properties of [htop] --------------------- -/

lemma htop_intro : forall h,
  ⊤ h :=
by
  move=> h //

lemma himpl_htop_r : forall H,
  H ==> ⊤ :=
by
  move=> H h //

lemma htop_eq :
  ⊤ = h∃ H, H :=
by
  srw (htop)

lemma hstar_htop_htop :
  ⊤ ∗ ⊤ = ⊤ :=
by
  apply himpl_antisym
  { apply himpl_htop_r }
  { srw -[1](hstar_hempty_r ⊤)
    apply himpl_frame_r ; apply himpl_htop_r }


/- -------------------- Properties of [hsingle] -------------------- -/

lemma hsingle_intro : forall p v,
  (p ~~> v) (Finmap.singleton p v) :=
by
  move=> p v //

lemma hsingl_inv : forall p v h,
  (p ~~> v) h →
  h = Finmap.singleton p v :=
by
  move=> p v h ; sapply

lemma disjoint_single_same_inv : forall {α : Type u} {β : α → Type v}
  (p : α) (v1 v2 : β p),
  Finmap.Disjoint (Finmap.singleton p v1) (Finmap.singleton p v2) →
  False :=
by
  move=> ? β p v1 v2
  srw (Finmap.Disjoint) (Not) => hDisj //


lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) ∗ (p ~~> v2) ==> ⌜False⌝ :=
by
  move=> p v1 v2 h ![h1 h2]
  srw [0](hsingle) => hh1 hh2 hDisj ?
  srw (hpure) (hexists) /==
  srw (hh1) (hh2) at hDisj
  apply (disjoint_single_same_inv p v1 v2 hDisj)


/- -------- Definitions and Properties of [haffine] and [hgc] -------- -/

def haffine (_ : hprop) :=
  True

lemma haffine_hany : forall H,
  haffine H :=
by
  move=> ? //

lemma haffine_hempty : haffine emp := haffine_hany emp

def hgc := htop -- Equivalent to [exists H, /[haffine H] ∗ H]

notation "/GC" => hgc

lemma haffine_hgc : haffine /GC := haffine_hany /GC

lemma himpl_hgc_r : forall H,
  haffine H →
  H ==> /GC :=
by
  move=> H ? h //

lemma hstar_hgc_hgc : /GC ∗ /GC = /GC := hstar_htop_htop
