import Ssreflect.Lang


/-
Inductive prim : Type :=
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
  | val_ptr_add : prim.
-/
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


inductive val where
  | val_unit : val
  | val_bool : Bool → val
  | val_int : Int → val
  | val_loc : loc → val
  | val_prim : prim → val
  | val_fun : var -> trm -> val
  | val_fiv : var -> var -> trm -> val
  | val_uninit : val
  | val_error : val
  with
inductive trm where
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
