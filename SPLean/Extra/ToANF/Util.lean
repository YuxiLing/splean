import SPLean.Theories.Lang

-- a simple delaborator for `String` and `Char` when they appear to be fully reduced
section StringDelab

open Lean PrettyPrinter Delaborator SubExpr

/-- Get `Char` from the first argument of a fully reduced `Char.mk` constructor. -/
def getCharFromCharMkInner (e : Expr) : Option Char := do
  let_expr UInt32.mk bv := e | failure
  let_expr BitVec.ofFin _ w := bv | failure
  let_expr Fin.mk _ n_ _ := w | failure
  let .lit (.natVal n) := n_ | failure
  return Char.ofNat n

/-- Get `Char` from a fully reduced `Char.mk` constructor. -/
def getCharFromCharMk (e : Expr) : Option Char := do
  let_expr Char.mk v _ := e | failure
  getCharFromCharMkInner v

/-- Get `String` from a list of fully reduced `Char.mk` constructors. -/
def getStringFromCharMks (e : Expr) : Option String := do
  let (_, l) ← e.listLit?
  let cs ← l.foldrM (fun ce cs => do
    let c ← getCharFromCharMk ce
    pure <| c :: cs) []
  return String.mk cs

@[delab app.Char.mk]
def delabCharMk : Delab := do
  let e ← getExpr
  let args := e.getAppArgs'
  guard <| args.size == 2
  let some c := getCharFromCharMkInner args[0]! | failure
  return quote c

@[delab app.String.mk]
def delabStringMk : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs' == 1
  let some res := getStringFromCharMks e.appArg! | failure
  return quote res

end StringDelab

open trm val in
def varset (countval? bounded? free? : Bool) (t : trm) : List var :=
  letI check x (p : List var) := if bounded? then insert x p else p.erase x
  match t with
  | trm_val v           => if countval? then val_case bounded? free? v else ∅
  | trm_var x           => if free? then { x } else ∅
  | trm_fun x t1        => check x <| varset countval? bounded? free? t1
  | trm_fix f x t1      => check f <| check x <| varset countval? bounded? free? t1
  | trm_app t1 t2
  | trm_seq t1 t2
  | trm_while t1 t2     => (varset countval? bounded? free? t1) ∪ (varset countval? bounded? free? t2)
  | trm_let x t1 t2
  | trm_alloc x t1 t2
  | trm_ref x t1 t2     => (varset countval? bounded? free? t1) ∪ (check x <| varset countval? bounded? free? t2)
  | trm_if t0 t1 t2     => (varset countval? bounded? free? t0) ∪ (varset countval? bounded? free? t1) ∪ (varset countval? bounded? free? t2)
  | trm_for x t1 t2 t3  => (varset countval? bounded? free? t1) ∪ (varset countval? bounded? free? t2) ∪ (check x <| varset countval? bounded? free? t3)
where val_case (bounded? free? : Bool) (v : val) : List var :=
  letI check x (p : List var) := if bounded? then insert x p else p.erase x
  match v with
  | val_fun x t1        => check x <| varset countval? bounded? free? t1
  | val_fix f x t1      => check f <| check x <| varset countval? bounded? free? t1
  | _                   => ∅

def pick_starting_fresh_var (t : trm) : var :=
  let vs := varset false true true t
  let tempvar n := "temp" ++ (String.replicate n '_')
  let n_ := Nat.findGreatest (fun n => vs.filter    -- using `.filter = ∅` is compatible with `Finset`
    (fun va => va.startsWith (tempvar (vs.length - n))) = ∅) vs.length
  tempvar (vs.length - n_)

open trm val in
def estimate_fuel (t : trm) : Nat :=
  match t with
  | trm_fun _ t1
  | trm_fix _ _ t1      => (estimate_fuel t1) + 1
  | trm_app t1 t2
  | trm_seq t1 t2
  | trm_while t1 t2
  | trm_let _ t1 t2
  | trm_alloc _ t1 t2
  | trm_ref _ t1 t2     => (Nat.max (estimate_fuel t1) (estimate_fuel t2)) + 1
  | trm_if t1 t2 t3
  | trm_for _ t1 t2 t3  => (Nat.max (estimate_fuel t1) (Nat.max (estimate_fuel t2) (estimate_fuel t3))) + 1
  | _                   => 2    -- might 1 is enough, but anyway

open trm val in
def trm_is_val_or_var (t : trm) : Bool :=
  match t with
  | trm_val _ => true
  | trm_var _ => true
  | _         => false
