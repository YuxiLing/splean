import SPLean.Extra.ToANF.Util

-- adapted from the code of the `reduce` function
namespace ReduceLess

open Lean Meta Elab

/-- `reduce` but with a customizable `skipCondition` to specify
    which subterms to skip during reduction. -/
partial def reduceLess (e : Expr) (skipCondition : Expr → MetaM Bool) (explicitOnly skipTypes skipProofs := true) : MetaM Expr :=
  let rec visit (e : Expr) : MonadCacheT Expr Expr MetaM Expr :=
    checkCache e fun _ => Core.withIncRecDepth do
      if (← (pure skipTypes <&&> isType e)) then
        return e
      else if (← (pure skipProofs <&&> isProof e)) then
        return e
      else if (← skipCondition e) then      -- newly added
        return e
      else
        let e ← whnf e
        match e with
        | Expr.app .. =>
          let f     ← visit e.getAppFn
          let nargs := e.getAppNumArgs
          let finfo ← getFunInfoNArgs f nargs
          let mut args  := e.getAppArgs
          for i in [:args.size] do
            if h : i < finfo.paramInfo.size then
              let info := finfo.paramInfo[i]
              if !explicitOnly || info.isExplicit then
                args ← args.modifyM i visit
            else
              args ← args.modifyM i visit
          if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isRawNatLit then
            return mkRawNatLit (args[0]!.rawNatLit?.get! + 1)
          else
            return mkAppN f args
        | Expr.lam ..        => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
        | Expr.forallE ..    => forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
        | Expr.proj n i s .. => return mkProj n i (← visit s)
        | _                  => return e
  visit e |>.run

end ReduceLess

namespace ANF

open val trm

abbrev SimpleANFM := ReaderT var (StateM Nat)

def anf_serialize (l : List (Option var × trm)) : trm → trm :=
  l.foldr (fun (x?, t1) t => match x? with
    | some x => trm_let x t1 t
    | none => trm_seq t1 t)

def trm_app_serialize (t : trm) (acc : List trm) : List trm := do
  match t with
  | trm_app t1 t2 => trm_app_serialize t1 (t2 :: acc)
  | _ => t :: acc

def anf_terminal (t : trm) : SimpleANFM (List (Option var × trm) × trm) := do
  if trm_is_val_or_var t
  then pure ([], t)
  else do
    let fresh ← get
    modify Nat.succ
    let x := (← read) ++ toString fresh
    pure ([(some x, t)], trm_var x)

-- having `fuel` is __super ugly__, but no better idea for how to avoid mutual recursion/explicit termination proof
def anf_main (fuel : Nat) (t : trm) : SimpleANFM (List (Option var × trm) × trm) :=
  -- previously, if not using `letI` then Lean cannot detect decreasing arg automatically;
  -- now with `fuel`, this becomes not important
  letI go (fue : Nat) (t : trm) : SimpleANFM trm := do
    let (l, t') ← anf_main fue t
    pure (anf_serialize l t')
  letI go_tmn (fue : Nat) (t : trm) : SimpleANFM (List (Option var × trm) × trm) := do
    let (l, t') ← anf_main fue t
    let (l', t'') ← anf_terminal t'
    pure (l ++ l', t'')
  if let .succ fuel := fuel then do
  match t with
  | trm_seq t1 t2       => do
    let (l1, t1') ← anf_main fuel t1
    let (l2, t2') ← anf_main fuel t2
    pure (l1 ++ [(none, t1')] ++ l2, t2')
  | trm_let x t1 t2     => do
    let (l1, t1') ← anf_main fuel t1
    let (l2, t2') ← anf_main fuel t2
    pure (l1 ++ [(some x, t1')] ++ l2, t2')

  | trm_app _ _         => do
    let args := trm_app_serialize t []
    let (ls, args) ← List.unzip <$> args.mapM (go_tmn fuel)
    if let hd :: tl := args then
      let res := tl.foldl (fun acc arg => trm_app acc arg) hd
      pure (ls.flatten, res)
    else pure ([], t) -- unreachable

  | trm_for x t1 t2 t3  => do
    let (l1, t1') ← go_tmn fuel t1
    let (l2, t2') ← go_tmn fuel t2
    let t3' ← go fuel t3
    pure (l1 ++ l2, trm_for x t1' t2' t3')

  | trm_while t1 t2     => do
    let t1' ← go fuel t1
    let t2' ← go fuel t2
    pure ([], trm_while t1' t2')

  | trm_alloc x t1 t2
  | trm_ref x t1 t2     => do
    let (l1, t1') ← go_tmn fuel t1
    let t2' ← go fuel t2
    match t with
    | trm_alloc _ _ _ => pure (l1, trm_alloc x t1' t2')
    | trm_ref _ _ _   => pure (l1, trm_ref x t1' t2')
    | _               => pure ([], t) -- unreachable

  | trm_if t0 t1 t2     => do
    let (l0, t0') ← go_tmn fuel t0
    let t1' ← go fuel t1
    let t2' ← go fuel t2
    pure (l0, trm_if t0' t1' t2')

  | _                   => anf_terminal t
  else pure ([], t)

def anf_main.go (t : trm) : SimpleANFM trm := do
  let (l, t') ← anf_main (estimate_fuel t) t
  pure (anf_serialize l t')

def anf_final (pf : var) (n : Nat) (t : trm) : trm :=
  (anf_main.go t).run pf |>.run' n

def anf (t : trm) : trm := anf_final (pick_starting_fresh_var t) 0 t

def anf_toplevel_aux (pf : var) (t : trm) : trm :=
  match t with
  | trm_fun x t1 => trm_fun x (anf_toplevel_aux pf t1)
  | _ => anf_final pf 0 t

def anf_toplevel (t : val) : val :=
  match t with
  | val_fun x t1 =>
    let pf := (pick_starting_fresh_var <| trm_fun x t1)
    val_fun x (anf_toplevel_aux pf t1)
  | val_fix f x t1 =>
    let pf := (pick_starting_fresh_var <| trm_fix f x t1)
    val_fix f x (anf_toplevel_aux pf t1)
  | _ => t

end ANF

-- syntax for defining ANF-transformed functions

open Lean Meta Elab in
private def ANF.skippingLangVal (e : Expr) : MetaM Bool := do
  let e ← whnf e
  match_expr e with
  | trm.trm_val _ => pure true
  | _ => pure false

-- a very specific `reduce` function that skips any evaluation on `val`
syntax "reduce_skip_val%" term : term

-- adapted from the code for `#reduce`
open Lean Meta Elab in
elab_rules : term
  | `(reduce_skip_val%%$tk $stx) =>
    withoutModifyingEnv do
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      withRef tk <| Meta.check e
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
        withTransparency (mode := TransparencyMode.default) <| ReduceLess.reduceLess e ANF.skippingLangVal (skipProofs := true) (skipTypes := true)

-- macro "lang_def'" n:ident ":=" l:lang : command => do
--   `(def $n:ident : val := reduce_skip_val% (anf_toplevel [lang| $l]))

-- WARNING: partial evaluation on monads via `reduce_skip_val%` or `conv`
-- (with a suitable collection of involved definitions to unfold) is very unstable!!!
-- It either fails with cryptic error messages
-- or produces large terms with recursors that cannot be further evaluated.
