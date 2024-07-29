import LeanLgtm.XSimp
import LeanLgtm.XChange
import LeanLgtm.Util
import LeanLgtm.SepLog
import LeanLgtm.WP1
import LeanLgtm.Lang


/- ============== Definitions for Arrays ============== -/

open val trm prim

def hheader (n : Int) (p : loc) : hprop :=
  p ~~> (val_int n)

lemma hheader_eq p n :
  (hheader n p) = (p ~~> (val_int n)) := by
  sdone

def hcell (v : val) (p : loc) (i : Int) : hprop :=
  ((p + 1 + (Int.natAbs i)) ~~> v) ∗ ⌜i >= 0⌝

lemma hcell_eq v p i :
  (hcell v p i) = ((p + 1 + (Int.natAbs i)) ~~> v) ∗ ⌜i >= 0⌝ := by
  sdone

lemma hcell_nonneg v p i :
  hcell v p i ==> hcell v p i ∗ ⌜i >= 0⌝ := by
  sby srw hcell_eq ; xsimp

def hseg (L : List val) (p : loc) (j : Int) : hprop :=
  match L with
  | []      => emp
  | x :: L' => (hcell x p j) ∗ (hseg L' p (j + 1))

def harray (L : List val) (p : loc) : hprop :=
  hheader (L.length) p ∗ hseg L p 0

lemma harray_eq p L :
  harray L p = h∃ n, ⌜n = L.length⌝ ∗ hheader n p ∗ hseg L p 0 := by
  sby srw harray ; xsimp ; xsimp

/- inversion lemma for hseg -/

lemma hseg_start_eq L p j1 j2 :
  j1 = j2 →
  hseg L p j1 ==> hseg L p j2 := by
  sdone


/- ================== Implementation of Arrays ================= -/

/- A simplified specification for non-negative pointer addition -/

lemma natabs_nonneg (p : Nat) (n : Int) :
  n ≥ 0 → (p + n).natAbs = p + n.natAbs := by
  omega

lemma triple_ptr_add_nonneg (p : loc) (n : Int) :
  n >= 0 →
  triple [lang| p ++ n]
    emp
    (fun r ↦ ⌜r = val_loc (p + Int.natAbs n)⌝) := by
  move=> ?
  apply (triple_conseq _ emp
    (fun r ↦ ⌜r = val_loc (Int.toNat (Int.natAbs (p + n)))⌝))
  apply triple_ptr_add
  { omega }
  { xsimp }
  xsimp ; xsimp ; subst r=> /==
  sby apply natabs_nonneg


/- Semantics of Low-Level Block Allocation -/

#check val_alloc

#check eval.eval_alloc
/- eval.eval_alloc (n : ℤ) (sa : state) (Q : val → state → Prop) :
  n ≥ 0 →
  (∀ (p : loc) (sb : state),
      sb = conseq val (make_list n.natAbs val_uninit) p →
      p ≠ null →
      Finmap.Disjoint sa sb →
      Q p (sb ∪ sa)) →
      eval sa (trm_app val_aloc n) Q
 -/

/- Heap predicate for describing a range of cells -/

def hrange (L : List val) (p : loc) : hprop :=
  match L with
  | []      => emp
  | x :: L' => (p ~~> x) ∗ (hrange L' (p + 1))

lemma hrange_intro L p :
  (hrange L p) (conseq L p) := by
  induction L generalizing p ; srw conseq hrange=> //
  apply hstar_intro=>//
  sby apply disjoint_single_conseq

lemma triple_alloc (n : Int) :
  n ≥ 0 →
  triple [lang| alloc n ]
    emp
    (funloc p ↦ hrange (make_list n.natAbs val_uninit) p ∗ ⌜p ≠ null⌝ ) := by
  move=> ?? [] ; apply eval.eval_alloc=>// > *
  apply (hexists_intro _ p)
  srw hstar_hpure_l Finmap.union_empty hstar_hpure_r => ⟨|⟨|⟩⟩ //
  subst sb ; apply hrange_intro


/- Low-level Implementation of arrays -/



def val_array_get : val := [lang|
  fun p i =>
    let p1 := p ++ 1 in
    let q := p1 ++ i in
    !q ]

def val_array_set : val := [lang|
  fun p i v =>
    let p1 := p ++ 1 in
    let q := p1 ++ i in
    q := v ]

/- Syntax for array operations -/


@[app_unexpander default_get] def unexpandGet : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $p] [lang| $i]) => `([lang| $p[$i]])
  | `($(_) $p:ident $i:ident) => `([lang| $p:ident[$i:ident]])
  | `($(_) $p:ident $i:num) => `([lang| $p:ident[$i:num]])
  | _ => throw ( )

@[app_unexpander default_set] def unexpandSet : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $p] [lang| $i] [lang| $v]) => `([lang| $p[$i] := $v])
  | _ => throw ( )

@[app_unexpander val_array_make] def unexpandArrMake : Lean.PrettyPrinter.Unexpander
  | `($(_) [lang| $n] [lang| $v]) => `([lang| mkarr $n, $v])
  | _ => throw ( )

-- set_option pp.notation false
#check [lang|
  let arr := mkarr 5, 1 in
  arr[4] := 2 ;
  arr[3]
  ]


/- ==================== Properties of Arrays ==================== -/

/- properties of [hseg] -/

lemma hseg_nil p j :
  hseg [] p j = emp := by
  sdone

lemma hseg_one v p j :
  hseg (v :: []) p j = hcell v p j := by
  sby srw hseg hseg ; xsimp

lemma hseg_cons v p j L :
  hseg (v :: L) p j = hcell v p j ∗ hseg L p (j + 1) := by
  sby srw hseg

lemma hseg_app L1 L2 p j :
  hseg (L1 ++ L2) p j =
  hseg L1 p j ∗ hseg L2 p (j + L1.length) := by
  induction L1 generalizing j with
  | nil         => srw hseg /== ; hsimp
  | cons _ _ ih =>
      sby dsimp ; srw ?hseg_cons ih -[4](add_comm 1) add_assoc ; hsimp


/- ------------------- Focus lemmas for [hseg] ------------------- -/

lemma list_cons_length (A : Type) (x : A) (L : List A) :
  (x :: L).length = 1 + L.length := by
  simp
  omega

lemma list_nil_length (A : Type) :
  ([] : List A).length = 0 := by sdone

lemma ofnat_plusone (n : Nat) :
  Int.ofNat (n + 1) = (Int.ofNat n) + 1 := by sdone

#check List.append_of_mem
lemma list_middle_inv (A : Type) (n : Nat) (l : List A) :
  n < l.length →
  exists (x : A) (l1 l2 : List A),
    l = l1 ++ x :: l2 ∧ l1.length = n := by
  induction n generalizing l with
  | zero       => move=> ? ; cases l => //
  | succ n' ih =>
      move=> hlen ; cases l with
      | nil => sdone
      | cons x l' =>
          have h : (n' < l'.length) := by srw list_cons_length at hlen ; omega
          apply ih in h=> [x' [l1 [l2]]] ?
          exists x', (x :: l1), l2 ; sdone

lemma nth_app_r {A : Type} (_ : Inhabited A) n (l1 l2 : List A) :
  n ≥ l1.length →
  (l1 ++ l2)[n]! = l2[n - l1.length]! := by
  elim: l1 n l2
  { sdone }
  sby move=> > ? []

#check List.getElem_of_append
lemma nth_middle (A : Type) (IA : Inhabited A) (n : Nat)
  (l1 l2 : List A) (x : A) :
  n = l1.length → (l1 ++ x :: l2)[n]! = x := by
  move=> ?
  sby srw nth_app_r

lemma cons_app {A : Type} (l1 l2 : List A) (x : A) :
  x :: l1 ++ l2 = x :: (l1 ++ l2) := by
  sdone

lemma update_app_r {A : Type} (l1 l2 : List A) n v :
  n ≥ l1.length →
  (l1 ++ l2).set n v = l1 ++ l2.set (n - l1.length) v := by
  elim: l1 l2 n v
  { sdone }
  move=> > ? >
  sby cases n

#check List.concat_eq_append
lemma update_middle (A : Type) (_ : Inhabited A) (n : Nat)
  (l1 l2 : List A) (x v : A) :
  n = l1.length → (l1 ++ x :: l2).set n v = (l1.concat v) ++ l2 := by
  move=> ? ; subst n=> /==
  sby srw update_app_r

lemma hseg_focus_relative (k : Nat) L p j (v : 0 <= k ∧ k < L.length):
  hseg L p j ==>
  hcell L[k]! p (j + k)
    ∗ (h∀ w, hcell w p (j + k) -∗ hseg (L.set k w) p j) := by
  move: v=> [] ? /list_middle_inv ![> ?] hlen
  move: (Eq.symm hlen) => /nth_middle hmid
  subst L ; srw (hmid _ w_2 w) hseg_app hseg_cons hlen -hstar_comm_assoc
  apply himpl_frame_r
  apply himpl_hforall_r => ?
  move: (Eq.symm hlen) => /(update_middle val _ k w_1 w_2 w) hset
  srw (hset _) ?List.concat_append ?hseg_app ?hseg_cons ?hlen
  sby xsimp

lemma add_Int.natAbs i j :
  0 <= i - j → j + Int.natAbs (i - j) = i := by omega

lemma nonneg_eq_abs (n : Int) :
  0 ≤ n → n.natAbs = n := by omega
    -- unfold Int.toNat Int.natAbs=> ?
    -- cases n <;> sdone

-- set_option pp.all true
lemma hseg_focus (i j : Int) L p (v : 0 <= i - j ∧ i - j < L.length) :
  0 <= i - j ∧ i - j < L.length →
  hseg L p j ==>
  hcell L[(i - j).natAbs]! p i
    ∗ (h∀ w, hcell w p i -∗ hseg (L.set (i - j).natAbs w) p j) := by
  -- move: v=> [] * ; xchange (hseg_focus_relative (i - j).natAbs) ; omega
  move=> [] * ; xchange (hseg_focus_relative (i - j).natAbs) ; omega
  srw add_Int.natAbs ; xsimp ; omega
  -- srw -(nonneg_eq_abs (i - j)) /=
  -- all_goals sorry

lemma harray_focus i L p (v : 0 <= i ∧ i < L.length) :
  0 <= i ∧ i < L.length →
  harray L p ==>
  hcell L[Int.natAbs i]! p i
    ∗ (h∀ w, hcell w p i -∗ harray (L.set (Int.natAbs i) w) p) := by
  move:v => [] *
  -- move=> [] *
  srw ?harray ; xchange (hseg_focus i) ; omega=> //==
  apply himpl_frame_r ; apply himpl_hforall_r => x
  xchange (hforall_specialize _ x)
  xsimp

lemma set_nth_same (A : Type) (IA : Inhabited A) (n : Nat) (l : List A) :
  n < l.length → l.set n l[n]! = l := by
  elim: l n;
  { sdone }
  move=> >? ; scase
  all_goals sdone

lemma harray_focus_read i L p :
  0 <= i ∧ i < L.length →
  harray L p ==>
  hcell L[Int.natAbs i]! p i ∗ (hcell L[Int.natAbs i]! p i -∗ harray L p) := by
  move=> [] *
  xchange (harray_focus i L p) => // ; xsimp
  xchange (hforall_specialize _ L[Int.natAbs i]!)
  srw set_nth_same
  xsimp
  omega


/- ========================= Triple rules for Arrays ========================= -/

open eval

set_option linter.hashCommand false
#hint_xapp triple_get
#hint_xapp triple_set

lemma triple_array_length_hheader (n : Int) (p : loc) :
  triple (trm_app val_array_length p)
    (hheader n p)
    (fun r ↦ ⌜r = n⌝ ∗ hheader n p) := by
    xwp
    srw hheader
    xapp

-- set_option pp.all true

lemma triple_array_get_hcell (p : loc) (i : Int) (v : val) :
  triple [lang| val_array_get p i]
    (hcell v p i)
    (fun r ↦ ⌜r = v⌝ ∗ hcell v p i) := by
    /- trm_apps val_array_get [p, i] -/
    xwp
    unfold hcell
    xpull
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby xapp; xsimp

lemma triple_array_set_hcell (p : loc) (i : Int) (v w : val) :
  triple (trm_app val_array_set p i v)
    (hcell w p i)
    (fun _ ↦ hcell v p i) := by
    xwp
    srw hcell
    xpull
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby unfold hcell ; xapp ; xsimp

lemma triple_array_get_hseg L (p : loc) (i j : Int) (_ : 0 <= i - j ∧ i - j < L.length) :
  triple [lang| val_array_get p i]
    (hseg L p j)
    (fun r ↦ ⌜r = L[(i - j).natAbs]!⌝ ∗ hseg L p j) := by
    xtriple
    xchange (hseg_focus i)=>//
    xapp triple_array_get_hcell
    xchange hforall_specialize
    rw [<- nonneg_eq_abs (i - j)] => /=
    xsimp=> //
    srw set_nth_same // ; omega

lemma triple_array_set_hseg L (p : loc) (i j : Int) (v : val) :
  0 <= i - j ∧ i - j < L.length →
  triple (trm_app val_array_set p i v)
    (hseg L p j)
    (fun _ ↦ hseg (L.set (Int.natAbs (i - j)) v) p j) := by
    move=> ?
    xtriple
    xchange (hseg_focus i)=>//
    xapp triple_array_set_hcell
    xchange hforall_specialize

lemma hseg_eq_hrange L p (k : Nat) :
  hseg L p k = hrange L (p + 1 + k) := by
  elim: L p k
  { sdone }
  move=> > ih >
  srw hrange hseg [2]add_assoc -ih hcell /==
  xsimp
  sby srw -hstar_assoc ; xsimp

lemma triple_array_fill (n : Int) L (p : loc) (i : Int) (v : val) :
  n = L.length →
  triple (trm_app val_array_fill p i n v)
    (hseg L p i)
    (fun _ ↦ hseg (make_list n.natAbs v) p i) := by
  srw val_array_fill
  elim: n L p i v=> a
  { elim: a=> > ? > ; xwp
    { xapp triple_gt ; xwp
      xif=> ? //
      xwp ; xval
      unfold make_list
      sorry }
    sorry }
  sdone

lemma triple_array_make_hseg (n : Int) (v : val) :
  n >= 0 →
  triple (trm_app val_array_make n v)
    emp
    (funloc p ↦ hheader n p ∗ hseg (make_list (n.natAbs) v) p 0) := by
  unfold val_array_make
  xwp
  xapp triple_add ; xwp
  xlet ; xwp
  xapp triple_alloc ; xwp
  xseq ; xwp
  sorry
  omega

lemma triple_array_get L (p : loc) (i : Int) (v : 0 <= i ∧ i < L.length) :
   triple (trm_app val_array_get p i)
    (harray L p)
    (fun r ↦ ⌜r = L[i.natAbs]!⌝ ∗ harray L p) := by
    xtriple
    srw harray ; xapp triple_array_get_hseg => /==
    xsimp

lemma triple_array_set L (p : loc) (i : Int) (v : val) :
  0 <= i ∧ i < L.length →
  triple (trm_app val_array_set p i v)
    (harray L p)
    (fun _ ↦ harray (L.set (Int.natAbs i) v) p) := by
    move=> ?
    xtriple
    srw ?harray ; xapp triple_array_set_hseg => /==
    xsimp

lemma triple_array_length L (p : loc) :
  triple (trm_app val_array_length p)
    (harray L p)
    (fun r ↦ ⌜r = val_int L.length⌝ ∗ harray L p) := by
    xtriple
    srw harray
    xapp triple_array_length_hheader
    xsimp

lemma make_list_len (n : Int) (v : val) :
  (make_list n.natAbs v).length = n.natAbs := by
  elim: n=> >
  { elim: a=> > //
    move=> ?
    sby srw make_list }
  elim: a=> > //
  move=> ? /=
  sby srw make_list

lemma triple_array_make (n : Int) (v : val) :
  n ≥ 0 →
  triple (trm_app val_array_make n v)
    emp
    (funloc p ↦ harray (make_list n.natAbs v) p) := by
  move=> ?
  xtriple
  srw harray
  xapp triple_array_make_hseg
  xsimp
  { sdone }
  sby srw make_list_len nonneg_eq_abs


/- Rules for [default_get] and [default_set] -/

instance : GetElem (List val) Int val (fun L i => 0 <= i ∧ i < L.length) where
    getElem vs i h := vs.get ⟨i.natAbs, by cases i <;> sdone⟩

-- set_option pp.all true
lemma triple_array_default_get (p : loc) (i : Int) :
  triple [lang| p[i]]
    (harray L p)
    (fun r ↦ ⌜r = L[i]!⌝ ∗ harray L p) := by
  xwp
  unfold harray
  xapp triple_le ; xwp
  xif=> /== ? ; xwp
  { xapp triple_array_length_hheader ; xwp
    xapp triple_lt ; xwp
    xif=> /== ?  ; xwp
    { srw -harray
      xapp triple_array_get ; xsimp
      srw -(nonneg_eq_abs i) //=
      unfold Nat.cast NatCast.natCast
      sorry }
    xwp ; xval ; xsimp ; sorry }
  xwp ; xval ; xsimp ; sorry

lemma set_keep_length (L : List val) i v :
  L.length = (L.set i v).length := by
  elim: L ; all_goals sdone

lemma set_out_of_bounds (L : List val) i v :
  i < 0 ∨ i ≥ L.length →
  L.set i v = L := by
  move=> [] ?
  { elim: L ; all_goals sdone }
  elim:L i ; sdone
  move=> > ? > ?
  scase: i ; all_goals sdone

lemma triple_array_default_set L (p : loc) (i : Int) (v : val) :
  triple [lang| p[i] := v]
    (harray L p)
    (fun _ ↦ harray (L.set (Int.natAbs i) v) p) := by
    xwp
    unfold harray
    xapp triple_le ; xwp
    xif=> /== ? ; xwp
    { xapp triple_array_length_hheader ; xwp
      xapp triple_lt ; xwp
      xif=> /== ? ; xwp
      { srw [2](set_keep_length L i.natAbs v) -?harray
        xapp triple_array_set }
      srw set_out_of_bounds ; xwp ; xval ; xsimp ; omega }
    xwp ; xval ; xsimp
    srw set_out_of_bounds // ; sorry

/- Rules and definitions for integer arrays -/

instance: GetElem (List Int) Int Int (fun L i => i.natAbs < L.length) :=
  ⟨fun xs i _ => xs[i.natAbs]⟩

example (L : List Int) (i : Int) (_ : i.natAbs < L.length) :
  L[i.natAbs]! = L[i]! := by
  rfl

/-
  · We define [GetElem] instance for [Int] ideceies via [Int.natAbs]. Now this is just
    def-equal to a regular [GetElem] instance
  · You have only one lemma `x[i](!) = x[i.natAbs](!)` to facilitate proofs
  · Now you can use this `[·]!` notation in your lemmas
  · You dont proof [triple_array_default] lemma, cuz it is just does not hold. Instead you
    proof [triple_array_int_default] directly
 -/

def harray_int (L : List Int) : loc → hprop :=
  harray (L.map val_int)

lemma triple_array_default_get_int (p : loc) (i : Int) (L : List Int) :
  triple [lang| p[i]]
    (harray_int L p)
    (fun r ↦ ⌜r =  val_int L[i]!⌝ ∗ harray_int L p) := by
  unfold harray_int ; xtriple
  xapp triple_array_default_get ; xsimp
  elim: L
  rw [List.map_nil]
  all_goals sorry
