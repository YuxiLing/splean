import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Common

import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.ArraysFun
import SPLean.Theories.Records

section find_index

open Theories prim val trm



/- First we put simple triple lemmas into our hint data base
   Those lemmas tell how to symbolically advance basic language instructions -/

#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get


namespace Lang

/- This is DSL term declaration. For now we only support reasoning about terms in SSA-normal form -/
lang_def incr :=
  fun p =>
    let x := !p in
    let x := x + 1 in
    p := x

-- set_option pp.all true in #print incr

/- We can extend the syntax of our languge on the fly with a new Theories operation [incr] -/
syntax "++" : uop
macro_rules
  | `([lang| ++ $a:lang]) => `(trm.trm_app incr [lang| $a])
@[app_unexpander incr] def unexpandIncr : Lean.PrettyPrinter.Unexpander := fun _ => `([uop| ++])

#hint_xapp triple_add -- add a triple lemma for pure addition to a hint database

@[xapp] -- Another way to add a triple lemma to a hint database
lemma incr_spec (p : loc) (n : Int) :
  { p ~~> n }
  [ ++p ]
  { p ~~> val_int (n + 1) } := by
  xstep triple_get -- Tactic for a one step of symbolic execution;
                   -- You can pass a specific triple lemma to guide the symbolic execution
  xstep            -- Or you can let the tactic choose the lemma for a current pgrogram from [xapp] hint database
  xstep

lang_def decr :=
  fun p =>
    let x := !p in
    let x := x - 1 in
    p := x


lemma decr_spec (p : loc) (n : Int) :
  { p ~~> n }
  [ decr p ]
  { p ~~> val_int (n - 1) } := by
  xstep triple_get
  xstep
  xstep

lang_def mysucc :=
  fun n =>
    let r := ref n in
    incr r;
    let x := !r in
    free r;
    x

lemma mysucc_spec (n : Int) :
  { ⌜True⌝ }
  [ mysucc n ]
  { v, ⌜v = val_int (n + 1)⌝ } := by
  xwp
  xlet
  xapp triple_ref_prim
  intros r
  xstep
  xstep
  xstep triple_free
  xval
  xsimp

lang_def myfun :=
  fun p  =>
    let f := fun_ u => incr p in
    f();
    f()

lemma myfun_spec (p : loc) (n : Int) :
  { p ~~> n }
  [ myfun p ]
  { p ~~> val_int (n + 2) } := by
  xwp
  xlet
  xapp triple_fun
  {sorry}
  {sorry}
  {
    sorry
  }


lang_def add_pointer :=
  fun p q =>
    let m := !q in
    for i in [0:m] {
      ++p
    }; !p

lemma add_pointer_spec (p q : loc) (n m : Int) (_ : m >= 0) :
  { p ~~> n ∗ q ~~> m }
  [ add_pointer p q ]
  { v, ⌜v = n+m⌝ ∗ ⊤  } := by
    xstep
    -- Tactic for a [for]-loop. This tactic should be supplied with a loop invariant [I].
    -- In this case [I] only captures a piece of the state, relevant to the loop body.
    -- The rest of the state would be framed automatically
    xfor (fun i => p ~~> n + i)
    { move=>*;
      xapp; -- Here rather than symbolically executing the top-most instruction in [incr], we
            -- Apply its specification lemma directly via [xapp] tactic
      xsimp; omega }
    move=> ? /=; xapp; xsimp

/- find_index: returns the index of the first occurence of `target` in
   `arr` or `size(arr)` if `target` is not an element of `arr` -/
lang_def findIdx :=
  fun arr target Z N =>
    ref ind := Z in
    while (
      let ind    := !ind in
      let indLN  := ind < N in
      if indLN then
        let arrind := arr[ind] in
        arrind != target
      else false) {
        ++ind
    };
    !ind

attribute [simp] is_true

set_option maxHeartbeats 1600000
lemma findIdx_spec (arr : loc) (f : ℤ -> ℝ) (target : ℝ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  target ∈ f '' ⟦z, n⟧ ->
  { arr(arr, i in N => f i) }
  [ findIdx arr target z n ]
  { v, ⌜ v = f.invFunOn ⟦z, n⟧ target ⌝ ∗ arr(arr, i in N => f i) } := by
  move=> inj fin
  xref;
  let cond := fun i : ℤ => (i < n ∧ f.invFunOn ⟦z, n⟧ target != i)
  xwhile_up (fun b i =>
    ⌜z <= i ∧ i <= n ∧ target ∉ f '' ⟦z, i⟧⌝ ∗
    p ~~> i ∗
    ⌜cond i = b⌝ ∗
    arr(arr, x in N => f x)) N
  { xsimp [(decide (cond z))]=> //; }
  { move=> b i
    xstep=> ?; srw cond /== => condE
    xstep
    xif=> //== iL
    { xstep; rotate_right
      { omega }
      xstep; xsimp=> //==
      scase: b condE=> /==
      { move=> /(_ iL) <-; apply Function.invFunOn_eq=> // }
      move=> _ /[swap] <-;
      srw Function.invFunOn_app_eq // }
    xval; xsimp=> //
    scase: b condE=> //==; omega }
  { move=> i;
    xapp=> /== ?? fE; srw cond /== => ? fInvE
    xsimp [(decide (cond (i + 1))), i+1]=> //
    { move=> ⟨|⟨|⟩⟩ <;> try omega
      move=> j *; scase: [j = i]=> [?|->]
      { apply fE <;> omega }
      move: fInvE=> /[swap] <-; srw Function.invFunOn_app_eq // }
    { omega }
    srw cond /== }
  move=> hv /=; xsimp=> i ?; srw cond=> /== fE
  xapp; xsimp[val_int i]
  srw fE //; scase: [i = n]=> [|?] //; omega

lemma findIdx_spec' (arr : loc) (f : Int -> ℝ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  i ∈ ⟦z, n⟧ ->
  { arr(arr, x in N => f x) }
  [ findIdx arr ⟨f i⟩ z n ]
  { v, ⌜ v = i ⌝ ∗ arr(arr, x in N => f x) } := by
  move=> inj iin
  xapp findIdx_spec; xsimp=> /=
  rw [Function.invFunOn_app_eq f inj iin]
