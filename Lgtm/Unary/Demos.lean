import Lean

import Lgtm.Unary.WP1

open val prim trm Unary

/- ################################################################# -/
/-* * Demo Programs -/

#hint_xapp triple_lt
#hint_xapp triple_get
-- #hint_xapp triple_ref
#hint_xapp triple_add
#hint_xapp triple_set
-- #hint_xapp triple_free

lang_def incr :=
  fun p =>
    let n := !p in
    let m := n + 1 in
    p := m

open Unary

@[xapp]
lemma triple_incr (p : loc) (n : Int) :
  {p ~~> n}
  [incr p]
  {p ~~> val_int (n + 1)} := by
  repeat (xwp; xapp)


lang_def mysucc :=
  fun n =>
    ref r := n in
    incr r;
    let x := !r in
    x

lemma triple_mysucc (n : Int) :
  { emp }
  [mysucc n]
  {v, ⌜ v = val_int (n + 1) ⌝} := by
  xwp ; -- xseq_xlet_if_needed ; xstruct_if_needed ; (apply xref_lemma)
  xref
  xwp ; xapp
  xwp ; xapp
  xwp ; xval
  xsimp_start
  xsimp_step ; xsimp_step
  -- xsimp_step
  apply (xsimp_r_hexists)
  xsimp_step
  try rev_pure
  try hide_mvars
  try hsimp


lang_def addp :=
  fun n m =>
    let k := !m in
    for i in [0:k] {
      incr n
    };
    !n

@[xapp]
lemma triple_addp (p q : loc) (m n : Int) :
  { p ~~> n ∗ q ~~> m ∗ ⌜m >= 0⌝ }
  [addp p q]
  { p ~~> val_int (n + m) ∗ q ~~> m } := by
  xwp; xapp=> ?
  xfor (fun i => p ~~> val_int (n + i))=> //
  { move=> ? _; xapp; xsimp; omega }
  xapp


lang_def mulp :=
  fun n m =>
    ref i :=  0 in
    ref ans := 0 in
    let m := !m in
    while (
      let i := !i in
      i < m) {
      addp ans n;
      incr i
    };
    !ans

def unloc : val -> loc | val_loc v => v | _ => panic! "unloc"

instance : Coe val loc := ⟨unloc⟩


-- instance : Coe Prop hProp := ⟨hpure⟩

elab "xsimpl" : tactic => do
  xsimp_step_l (<- XSimpRIni)

open Lean Lean.Expr Lean.Meta Qq
open Lean Elab Command Term Meta Tactic

macro_rules | `(tactic| ssr_triv ) => `(tactic| congr; omega)
macro_rules | `(tactic| ssr_triv ) => `(tactic| constructor=> //)

lemma triple_mulp (p q : loc) (m n : Int) :
  { p ~~> n ∗ q ~~> m ∗ ⌜m > 0 ∧ n >= 0⌝ }
  [mulp p q]
  {ans, ⌜ans = n * m⌝ ∗ ⊤ } := by
  xwp ; xref=> ?
  xwp ; xref
  xwp ; xapp
  xwhile_up (fun b j => p ~~> n ∗ q ~~> m ∗ p_1 ~~> j ∗ p_2 ~~> n * j ∗ ⌜(b = decide (j < m)) ∧ 0 <= j ∧ j <= m⌝) m
  { xsimp=> // }
  { sby move=>>; xwp; xapp=> ?; xapp; xsimp }
  { move=> X; xwp; xapp=> []??
    xapp; xsimp=> //
    sby srw Int.mul_add }
  move=> ? /=; xsimp=> a /== * -- here we need to do [xsimp] before [xapp]
                               -- to introduce variable [a], which is needed
                               -- to instantiate the `ans`
  sby xapp; admit
  --xsimp --same xsimp bug as in [triple_mysucc]
