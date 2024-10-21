import Mathlib.Data.Int.Interval
import Mathlib.Tactic

import Lgtm.Unary.WP1
import Lgtm.Unary.Lang
import Lgtm.Unary.ArraysFun

section find_index

open Unary prim val trm

/- [find_index] Implementation -/

lang_def val_or :=
  fun a b =>
    if a then true else b

syntax " || " : bop

macro_rules
  | `([lang| $a:lang || $b:lang]) => `(trm.trm_app val_or [lang| $a] [lang| $b])

@[app_unexpander val_or] def unexpandOr : Lean.PrettyPrinter.Unexpander := fun _ => `([bop| ||])

lang_def val_and :=
  fun a b =>
    if a then b else false

syntax " && " : bop

macro_rules
  | `([lang| $a:lang && $b:lang]) => `(trm.trm_app val_and [lang| $a] [lang| $b])

@[app_unexpander val_or] def unexpandAnd : Lean.PrettyPrinter.Unexpander := fun _ => `([bop| &&])


-- @[app_unexpander trm_app] def unexpandApp : Lean.PrettyPrinter.Unexpander := fun x => do


@[xapp]
lemma or_spec (a b : Bool) :
  { emp }
  [ a || b ]
  { v, ⌜v = (a || b)⌝ } := by
  xwp; xif=> -><;> xwp<;> xval <;> xsimp

@[xapp]
lemma and_spec (a b : Bool) :
  { emp }
  [ a && b ]
  { v, ⌜v = (a && b)⌝ } := by
  xwp; xif=> -><;> xwp<;> xval <;> xsimp

lang_def val_or_eq :=
  fun p b =>
    let v := !p in
    let v := v || b in
    p := v

syntax " ||= " : bop

macro_rules
  | `([lang| $a:lang ||= $b:lang]) => `(trm.trm_app val_or_eq [lang| $a] [lang| $b])

@[app_unexpander val_or_eq] def unexpandOrEq : Lean.PrettyPrinter.Unexpander := fun _ => `([bop| ||=])

@[xapp]
lemma or_eq_spec (a b : Bool) (p : loc) :
  { p ~~> a }
  [ p ||= b ]
  { v, p ~~> (b || a) } := by
  xwp; xapp; xwp; xapp; xwp; xapp
  xsimp; srw Bool.or_comm

lang_def val_add_eq :=
  fun p b =>
    let v := !p in
    let v := v + b in
    p := v

syntax " += " : bop

macro_rules
  | `([lang| $a:lang += $b:lang]) => `(trm.trm_app val_add_eq [lang| $a] [lang| $b])

@[app_unexpander val_add_eq] def unexpandAddEq : Lean.PrettyPrinter.Unexpander := fun _ => `([bop| +=])

@[xapp]
lemma add_eq_spec (a b : ℝ) (p : loc) :
  { p ~~> a }
  [ p += b ]
  { v, p ~~> (b + a) } := by
  xwp; xapp; xwp; xapp triple_addr; xwp; xapp
  xsimp; srw add_comm


namespace Lang
lang_def incr :=
  fun p =>
    let x := !p in
    let x := x + 1 in
    p := x

lemma incr_spec (p : loc) (n : Int) :
  { p ~~> n }
  [ incr p ]
  { p ~~> val.val_int (n + 1) } := by
  xwp; xapp
  xwp; xapp
  xwp; xapp

/- find_index: returns the index of the last occurence of `target` in
   `arr` or `-1` if `target` is not an element of `arr` -/
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
        incr ind
    };
    let res := !ind in
    res

abbrev to_real (v : val) : ℝ :=
  match v with
  | val_real n => n
  | _ => 0

abbrev to_int (v : val) : ℤ :=
  match v with
  | val_int n => n
  | _ => -1

instance : Coe ℝ val := ⟨val_real⟩
instance : Coe val ℝ := ⟨to_real⟩
instance : Coe val ℤ := ⟨to_int⟩

-- #hint_xapp triple_arrayFun_length ????
-- #hint_xapp triple_ref
#hint_xapp triple_get
#hint_xapp triple_lt
#hint_xapp triple_sub
#hint_xapp triple_neq
-- #hint_xapp triple_free
#hint_xapp incr_spec
#hint_xapp triple_arrayFun_length
#hint_xapp triple_harrayFun_get

attribute [simp] is_true


set_option maxHeartbeats 1600000
lemma findIdx_spec (arr : loc) (f : Int -> ℝ) (target : ℝ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  target ∈ f '' ⟦z, n⟧ ->
  { arr(arr, x in N => f x) }
  [ findIdx arr target z n ]
  { v, ⌜ v = f.invFunOn ⟦z, n⟧ target ⌝ ∗ arr(arr, x in N => f x) } := by
  move=> inj fin
  -- xwp; xapp triple_arrayFun_length
  xwp; xref
  let cond (i : ℤ) := (i < N ∧ f.invFunOn ⟦0, (N : ℤ)⟧ target != i)
  xwhile_up (fun b i =>
    ⌜z <= i ∧ i <= n ∧ target ∉ f '' ⟦z, i⟧⌝ ∗
    p ~~> i ∗
    ⌜cond i = b⌝ ∗
    arr(arr, x in N => f x)) N
  { xsimp [(decide (cond z))]=> //; }
  { move=> b i
    xwp; xapp=> ?; srw cond /== => condE
    xwp; xapp
    xwp; xif=> //== iL
    { xwp; xapp; rotate_right
      { omega }
      xwp; xapp; xsimp=> //==
      scase: b condE=> /==
      { move=> /(_ iL) <-; apply Function.invFunOn_eq=> // }
      move=> _ _ /[swap] <-;
      srw Function.invFunOn_app_eq // }
    xwp; xval; xsimp=> //
    scase: b condE=> //==; omega }
  { move=> i;
    xapp=> /== ?? fE ?; srw cond /== => ? fInvE
    xsimp [(decide (cond (i + 1))), i+1]=> //
    { move=> ⟨|⟨|⟩⟩ <;> try omega
      move=> j *; scase: [j = i]=> [?|->]
      { apply fE <;> omega }
      move: fInvE=> /[swap] <-; srw Function.invFunOn_app_eq // }
    { omega }
    srw cond /== }
  move=> hv /=; xsimp=> i ?; srw cond=> /== fE
  sdo 2 (xwp; xapp)
  xwp; xval; xsimp
  srw fE //; scase: [i = n]=> [|?] //; omega

lemma findIdx_spec_out (arr : loc) (f : Int -> ℝ) (target : ℝ)
  (z n : ℤ) (_ : z <= n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  Set.InjOn f ⟦z, n⟧ ->
  target ∉ f '' ⟦z, n⟧ ->
  { arr(arr, x in N => f x) }
  [ findIdx arr target z n ]
  { v, ⌜ v = val_int n ⌝ ∗ arr(arr, x in N => f x) } := by
  move=> ? img
  xwp; xref
  let cond (i : ℤ) := (i < N ∧ target != f i)
  xwhile_up (fun b i =>
    ⌜z <= i ∧ i <= n ∧ target ∉ f '' ⟦z, i⟧⌝ ∗
    p ~~> i ∗
    ⌜cond i = b⌝ ∗
    arr(arr, x in N => f x)) N
  { xsimp [(decide (cond z))]=> // }
  { move=> b i
    xwp; xapp=> ?; srw cond /== => condE
    xwp; xapp
    xwp; xif=> //== iL
    { xwp; xapp; rotate_left
      { omega }
      xwp; xapp; xsimp=> //==
      scase: b condE=> /==
      { move=> -> // }
      move=> _ _ /[swap] <- // }
    xwp; xval; xsimp=> //
    scase: b condE=> //==; omega }
  { move=> i;
    xapp=> /== ?? fE ?; srw cond /== => ? fInvE
    xsimp [(decide (cond (i + 1))), i+1]=> //
    { move=> ⟨|⟨|⟩⟩ <;> try omega
      move=> j *; scase: [j = i]=> [?|->]
      { apply fE <;> omega }
      move: fInvE=> /[swap] <- // }
    { omega }
    srw cond /== }
  move=> hv /=; xsimp=> i ?; srw cond=> /== fE
  sdo 2 (xwp; xapp)
  xwp; xval; xsimp
  scase: [i = n]=> [?|?] //;
  move: img; srw fE //== <;> try omega
  move=> /(_ i)=> // H
  specialize H ?_ ?_=> //; omega

lang_def searchIdx :=
  fun arr target Z N =>
    let arr0 := arr[Z] in
    let cnd := target < arr0 in
    if cnd then
      len arr
    else
      let Z' := Z + 1 in
      let ind := ref Z' in
      while (
        let ind    := !ind in
        let indLN  := ind < N in
        if indLN then
          let arrind := arr[ind] in
          arrind <= target
        else false) {
          incr ind
      };
      let res := !ind in
      free ind ;
      let res := res - 1 in
      res

set_option maxHeartbeats 1600000
lemma searchIdx_spec (arr : loc) (f : Int -> ℝ) (target : ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  MonotoneOn f ⟦z, n⟧ ->
  f z <= target ∧ target < f (n-1) ->
  { arr(arr, x in N => f x) }
  [ searchIdx arr target z n ]
  { v, ⌜
    to_int v ∈ ⟦z, n-1⟧ ∧ f v <= target ∧ target < f (v + 1) ⌝ ∗ arr(arr, x in N => f x) } := by
  move=> mon tgt
  xwp; xapp <;> try omega
  xwp; xapp triple_ltr
  xwp; xif=> //== <;> try omega
  { srw lt_iff_not_ge // }
  move=> _; xwp; xapp
  xwp; xapp=> p
  let cond (i : ℤ) := (z< i ∧ i < n ∧ f i <= target)
  xwhile_up (fun b i =>
    ⌜z < i ∧ i <= n ∧ ∀ x ∈ ⟦z, i⟧, f x <= target⌝ ∗
    p ~~> i ∗
    ⌜cond i = b⌝ ∗
    arr(arr, x in N => f x)) N
  { xsimp [(decide (cond (z + 1)))]=> //== ⟨|⟩; omega
    move=> z' *; shave<-//: z = z'; omega }
  { move=> b i
    xwp; xapp=> ih; srw cond /== => condE
    xwp; xapp
    xwp; xif=> //== iL
    { xwp; xapp; rotate_left
      { omega }
      xwp; xapp triple_ler; xsimp=> //== }
    xwp; xval; xsimp=> //
    scase: b condE=> //==; omega }
  { move=> i;
    xapp=> /== ?? fE ?; srw cond /== => ? fInvE
    xsimp [(decide (cond (i + 1))), i+1]=> //
    { move=> ⟨|⟨|⟩⟩ <;> try omega
      move=> j *; scase: [j = i]=> [?|//]
      apply fE <;> omega }
    omega }
  move=> hv /=; xsimp=> i ![?? ih]; srw cond=> /== fE
  sdo 3 (xwp; xapp)
  xwp; xval; xsimp
  simp [to_int]=> ⟨|⟨|⟩⟩;
  { scase: [i = n]=> ? <;> subst_vars
    { omega }
    specialize ih (i-1) ?_
    { simp; omega }
    scase: tgt=> _; move=> /not_lt_of_le // }
  { apply ih=> /==; omega }
  apply fE; omega
  srw lt_iff_not_ge=> ?; shave ?: i = n; omega
  subst_vars; specialize ih (i-1) ?_
  { simp; omega }
  scase: tgt=> _; move=> /not_lt_of_le //

lemma searchIdx_spec' (arr : loc) (f : ℤ -> ℝ) (target : ℝ)
  (z n : ℤ) (_ : z < n) (_ : 0 <= z) (N : ℕ) (_ : n <= N) :
  MonotoneOn f ⟦z, n⟧ ->
  i ∈ ⟦z,n-1⟧ ->
  f i <= target ∧ target < f (i + 1) ->
  { arr(arr, x in N => f x) }
  [ searchIdx arr target z n ]
  { v, ⌜ v = i ⌝ ∗ arr(arr, x in N => f x) } := by
  move=> mon /== ?? tg gt *; xapp searchIdx_spec=> /==;
  scase: x <;> simp [to_int] <;> try omega
  { move=> // j ????
    shave: f i < f (j + 1) ∧ f j < f (i + 1)
    { move=> ⟨|⟩ <;> linarith }
    -- #check
    scase=> /mon.reflect_lt /== ? /mon.reflect_lt /== ?
    shave->: i = j; omega; xsimp }
  shave ?: f z <= f i; apply mon=> /== <;> try omega
  shave ?: f (i + 1) <= f (n -1); apply mon=> /== <;> try omega
  constructor <;> linarith


end Lang

end find_index
