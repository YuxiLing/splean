import Lean

import LeanLgtm.WP1

open val prim trm

/- ################################################################# -/
/-* * Demo Programs -/

lang_def incr :=
  fun p =>
    let n := !p in
    let m := n + 1 in
    p := m

@[xapp]
lemma triple_incr (p : loc) (n : Int) :
  {p ~~> n}
  [incr(p)]
  {p ~~> n + 1} := by
  sdo 3 (xwp; xapp)

lang_def mysucc :=
  fun n =>
    let r := ref n in
    incr r;
    let x := !r in
    free r;
    x
-- set_option pp.notation false
-- set_option pp.explicit true
-- set_option pp.funBinderTypes true
-- set_option trace.xsimp true

lemma triple_mysucc (n : Int) :
  { emp }
  [mysucc n]
  {v, ⌜ v = n + 1 ⌝} := by
  sdo 4 (xwp; xapp);
  xwp; xval; xsimp=> //

lang_def addp :=
  fun n m =>
    let m := !m in
    for i in [0:m] {
      incr n
    };
    !n

@[xapp]
lemma triple_addp (p q : loc) (m n : Int) :
  { p ~~> n ∗ q ~~> m ∗ ⌜m >= 0⌝ }
  [addp p q]
  { p ~~> n + m ∗ q ~~> m } := by
  xwp; xapp=> ?
  xfor (fun i => p ~~> n + i)
  { move=> ? _; xapp; xsimp; omega }
  xapp_pre
  eapply xapp_lemma; xapp_pick;
  rotate_right;
  xsimp_start
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xsimp_step
  xapp; xsimp


lang_def mulp :=
  fun n m =>
    let i := ref 0 in
    let ans := ref 0 in
    let m := !m in
    while (
      let i := !i in
       i < m) {
      (addp ans n);
      (incr i)
    };
    !ans

def unloc : val -> loc | val_loc v => v | _ => panic! "unloc"

instance : Coe val loc := ⟨unloc⟩

abbrev lock (a : α) := a

-- instance : Coe Prop hprop := ⟨hpure⟩

elab "xsimpl" : tactic => do
  xsimp_step_l (<- XSimpRIni)

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic


-- def rfll (mvarId : MVarId) : TacticM Unit := do
--   mvarId.withContext do
--     mvarId.checkNotAssigned `refl
--     let targetType ← mvarId.getType'
--     unless targetType.isAppOfArity ``Eq 3 do
--       throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
--     let lhs ← instantiateMVars targetType.appFn!.appArg!
--     let rhs ← instantiateMVars targetType.appArg!
--     rhs.mvarId! lhs
--     mvarId.instantiateMVars
--   let gs <- getUnsolvedGoals
--   for g in gs do g.instantiateMVars
    -- let gs <-


    -- let success ← withAssignableSyntheticOpaque $ isDefEq lhs rhs
    -- unless success do
    --   throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    -- let us := targetType.getAppFn.constLevels!
    -- let α := targetType.appFn!.appFn!.appArg!
    -- mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)

macro_rules | `(tactic| ssr_triv ) => `(tactic| omega)

#hint_xapp triple_lt
-- set_option trace.xsimp true
-- set_option pp.all true
lemma triple_mulp (p q : loc) (m n : Int) :
  { p ~~> n ∗ q ~~> m ∗ ⌜m > 0 ∧ n >= 0⌝ }
  [mulp p q]
  {ans, ⌜ans = n * m⌝ ∗ ⊤ } := by
  xwp; xapp=> ? i
  xwp; xapp=> ans
  xwp; xapp
  xwhile_up (fun b j => p ~~> n ∗ q ~~> m ∗ i ~~> j ∗ ans ~~> n * j ∗ ⌜(b = decide (j < m)) ∧ 0 <= j ∧ j <= m⌝) m
  { xsimp; constructor=> // }
  { sby move=>>; xwp; xapp=> ?; xapp; xsimp }
  { move=> X; xwp; xapp=> []??
    xapp; xsimp=> //
    { sby srw Int.mul_add }
    constructor=> // }
  move=> ? /=; xsimp=> a ?
  xapp; xsimp; congr; simp_all; omega

  -- xapp
  -- xapp; run_tac (do
  --   let g <- getMainGoal
  --   withAssignableSyntheticOpaque $ rfll g
  -- )
  -- rfl
  -- xsimp_step

  -- xsimp_step
  -- xsimp_step
  -- xsimp_step
  -- xsimp_step
  -- foo=> //
