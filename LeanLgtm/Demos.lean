import Lean

import LeanLgtm.WP1

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
  xwp; xval; xsimp
