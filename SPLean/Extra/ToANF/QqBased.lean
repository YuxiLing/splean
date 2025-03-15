import SPLean.Extra.ToANF.Util
import Qq

open Qq Lean

namespace ANFQ

open val trm

def pick_starting_fresh_var_Q (t : Q(trm)) (init_vars : List Q(var) := []) : var :=
  let init_vars' := init_vars.filterMap (fun va =>
    if let .lit (.strVal x) := va then some x else none)
  let vs : List String := Expr.foldlM (m := Id) (fun l sube =>
    if let .lit (.strVal x) := sube then x :: l else l) init_vars' t
  let tempvar n := "temp" ++ (String.replicate n '_')
  let n_ := Nat.findGreatest (fun n => vs.filter    -- using `.filter = ∅` is compatible with `Finset`
    (fun va => va.startsWith (tempvar (vs.length - n))) = ∅) vs.length
  tempvar (vs.length - n_)

partial def trm_app_serialize_Q (t : Q(trm)) (acc : List Q(trm)) : MetaM (List Q(trm)) := do
  match t with
  | ~q(trm_app $t1 $t2) => trm_app_serialize_Q t1 (t2 :: acc)
  | _ => pure <| t :: acc

abbrev SimpleANFM := ReaderT var (StateT Nat MetaM)   -- `Qq` only works at `MetaM`?

def trm_is_val_or_var_Q (t : Q(trm)) : Bool :=
  match_expr t with
  | trm_val _ => true
  | trm_var _ => true
  | _         => false

def trm_is_val_or_var_Q' : Q(trm) → MetaM Bool
  | ~q(trm_val _)
  | ~q(trm_var _) => return true
  | _         => return false

def anf_serialize (l : List (Option Q(var) × Q(trm))) : Q(trm) → Q(trm) :=
  l.foldr (fun (x?, t1) t => match x? with
    | some x => q(trm_let $x $t1 $t)
    | none => q(trm_seq $t1 $t))

def anf_terminal (t : Q(trm)) : SimpleANFM (List (Option Q(var) × Q(trm)) × Q(trm)) := do
  if trm_is_val_or_var_Q t
  then pure ([], t)
  else do
    let fresh ← get
    modify Nat.succ
    let x : Q(var) := mkStrLit <| (← read) ++ toString fresh
    pure ([(some x, t)], q(trm_var $x))

partial def anf_main (t : Q(trm)) : SimpleANFM (List (Option Q(var) × Q(trm)) × Q(trm)) :=
  let go (t : Q(trm)) : SimpleANFM Q(trm) := do    -- if not using `letI` then Lean cannot detect decreasing arg automatically
    let (l, t') ← anf_main t
    pure (anf_serialize l t')
  let go_tmn (t : Q(trm)) : SimpleANFM (List (Option Q(var) × Q(trm)) × Q(trm)) := do
    let (l, t') ← anf_main t
    let (l', t'') ← anf_terminal t'
    pure (l ++ l', t'')
  match t with
  | ~q(trm_seq $t1 $t2)         => do
    let (l1, t1') ← anf_main t1
    let (l2, t2') ← anf_main t2
    pure (l1 ++ [(none, t1')] ++ l2, t2')
  | ~q(trm_let $x $t1 $t2)      => do
    let (l1, t1') ← anf_main t1
    let (l2, t2') ← anf_main t2
    pure (l1 ++ [(some x, t1')] ++ l2, t2')

  | ~q(trm_app _ _)             => do
    let args ← trm_app_serialize_Q t []
    let (ls, args) ← List.unzip <$> args.mapM go_tmn
    let hd :: tl := args | failure
    let res ← tl.foldlM (fun acc arg => do pure q(trm_app $acc $arg)) hd
    pure (ls.flatten, res)

  | ~q(trm_for $x $t1 $t2 $t3)  => do
    let (l1, t1') ← go_tmn t1
    let (l2, t2') ← go_tmn t2
    let t3' ← go t3
    pure (l1 ++ l2, q(trm_for $x $t1' $t2' $t3'))

  | ~q(trm_while $t1 $t2)       => do
    let t1' ← go t1
    let t2' ← go t2
    pure ([], q(trm_while $t1' $t2'))

  | ~q(trm_alloc $x $t1 $t2)    => do
    let (l1, t1') ← go_tmn t1
    let t2' ← go t2
    pure (l1, q(trm_alloc $x $t1' $t2'))
  | ~q(trm_ref $x $t1 $t2)      => do
    let (l1, t1') ← go_tmn t1
    let t2' ← go t2
    pure (l1, q(trm_ref $x $t1' $t2'))

  | ~q(trm_if $t0 $t1 $t2)      => do
    let (l0, t0') ← go_tmn t0
    let t1' ← go t1
    let t2' ← go t2
    pure (l0, q(trm_if $t0' $t1' $t2'))

  | _                   => anf_terminal t

def anf_main.go (t : Q(trm)) : SimpleANFM Q(trm) := do
  let (l, t') ← anf_main t
  pure (anf_serialize l t')

def anf_final (pf : var) (n : Nat) (t : Q(trm)) : MetaM Q(trm) :=
  (anf_main.go t).run pf |>.run' n

def anf (t : Q(trm)) : MetaM Q(trm) := anf_final (pick_starting_fresh_var_Q t) 0 t

-- for `val_funs` and `val_fixs`, we need to make sure that they will be "recovered" after ANF transformation
-- similar for `trm_funs` and `trm_fixs`

partial def anf_toplevel_aux (pf : var) (t : Q(trm)) : MetaM Q(trm) := do
  match t with
  | ~q(trm_fun $x $t1) =>
    let res ← anf_toplevel_aux pf t1
    pure q(trm_fun $x $res)
  | ~q(trm_funs $xs $t1) =>
    let res ← anf_toplevel_aux pf t1
    pure q(trm_funs $xs $res)
  | ~q(trm_fix $f $x $t1) =>
    let res ← anf_toplevel_aux pf t1
    pure q(trm_fix $f $x $res)
  | ~q(trm_fixs $f $xs $t1) =>
    let res ← anf_toplevel_aux pf t1
    pure q(trm_fixs $f $xs $res)
  | _ => anf_final pf 0 t

partial def anf_toplevel (t : Q(val)) : MetaM Q(val) := do
  match t with
  | ~q(val_fun $x $t1) =>
    let pf := pick_starting_fresh_var_Q t1 [x]
    let res ← anf_toplevel_aux pf t1
    pure q(val_fun $x $res)
  | ~q(val_fix $f $x $t1) =>
    let pf := pick_starting_fresh_var_Q t1 [f, x]
    let res ← anf_toplevel_aux pf t1
    pure q(val_fix $f $x $res)
  | ~q(val_funs $xs $t1) =>
    let pf := pick_starting_fresh_var_Q t1 (xs.listLit?.map Prod.snd |>.getD [])
    let res ← anf_toplevel_aux pf t1
    pure q(val_funs $xs $res)
  | ~q(val_fixs $f $xs $t1) =>
    let pf := pick_starting_fresh_var_Q t1 (f :: (xs.listLit?.map Prod.snd |>.getD []))
    let res ← anf_toplevel_aux pf t1
    pure q(val_fixs $f $xs $res)
  | _ => pure t

end ANFQ

open Lean Meta Elab in
def anf_meta (l : TSyntax `lang) : Term.TermElabM Expr := do
  let res ← Term.elabTerm (← `([lang| $l ])) (mkConst ``val)
  Term.synthesizeSyntheticMVarsNoPostponing
  let res ← Term.ensureHasType (.some <| mkConst ``val) res
  let res ← instantiateMVars res
  ANFQ.anf_toplevel res

open Lean Meta Elab in
def define_anf_val (n : Ident) (l : TSyntax `lang) : Command.CommandElabM Unit := do
  let e ← Command.liftTermElabM <| anf_meta l
  Command.liftCoreM do
    addAndCompile <| Declaration.defnDecl <|
      mkDefinitionValEx n.getId [] (mkConst ``val) e (Lean.ReducibilityHints.regular 0)
      (DefinitionSafety.safe) []
