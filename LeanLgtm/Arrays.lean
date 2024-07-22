import LeanLgtm.XSimp
import LeanLgtm.XChange
import LeanLgtm.Util
import LeanLgtm.SepLog
import LeanLgtm.WP1


/- ============== Definitions for Arrays ============== -/

open val
open trm

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
  triple (trm_app prim.val_ptr_add p n)
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
  triple (trm_app val_alloc n)
    emp
    (funloc p ↦ hrange (make_list n.natAbs val_uninit) p ∗ ⌜p ≠ null⌝ ) := by
  move=> ?? [] ; apply eval.eval_alloc=>// > *
  apply (hexists_intro _ p)
  srw hstar_hpure_l Finmap.union_empty hstar_hpure_r => ⟨|⟨|⟩⟩ //
  subst sb ; apply hrange_intro


/- Low-level Implementation of arrays -/

def val_array_length : val := [lang|
  fun p => !p ]

def val_array_get : val := [lang|
  fun p i =>
    let p1 := val_ptr_add p 1 in
    let q := val_ptr_add p1 i in
    !q ]

def val_array_set : val := [lang|
  fun p i v =>
    let p1 := val_ptr_add p 1 in
    let q := val_ptr_add p1 i in
    q := v ]

def val_array_fill : val := [lang|
  fix f p i n v =>
    let b := n > 0 in
    if b then
      val_array_set p i v ;
      let m := n - 1 in
      let j := i + 1 in
      f p j m v
    end ]

def val_array_make : val := [lang|
  fun n v =>
    let m := n + 1 in
    let p := val_alloc m in
    val_set p n ;
    val_array_fill p 0 n v ;
    p ]

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

lemma hseg_focus_relative (k : Nat) L p j :
  0 <= k ∧ k < L.length →
  hseg L p j ==>
  hcell L[k]! p (j + k)
    ∗ (h∀ w, hcell w p (j + k) -∗ hseg (L.set k w) p j) := by
  move=> [] ? /list_middle_inv ![> ?] hlen
  move: (Eq.symm hlen) => /nth_middle hmid
  subst L ; srw (hmid _ w_2 w) hseg_app hseg_cons hlen -hstar_comm_assoc
  apply himpl_frame_r
  apply himpl_hforall_r => ?
  move: (Eq.symm hlen) => /(update_middle val _ k w_1 w_2 w) hset
  srw (hset _) ?List.concat_append ?hseg_app ?hseg_cons ?hlen
  sby xsimp

lemma add_Int.natAbs i j :
  0 <= i - j → j + Int.natAbs (i - j) = i := by omega

lemma hseg_focus (i j : Int) L p :
  0 <= i - j ∧ i - j < L.length →
  hseg L p j ==>
  hcell L[Int.natAbs (i - j)]! p i
    ∗ (h∀ w, hcell w p i -∗ hseg (L.set (Int.natAbs (i - j)) w) p j) := by
  move=> [] * ; xchange (hseg_focus_relative (Int.natAbs (i - j))) ; omega
  sby srw add_Int.natAbs ; xsimp

lemma harray_focus i L p :
  0 <= i ∧ i < L.length →
  harray L p ==>
  hcell L[Int.natAbs i]! p i
    ∗ (h∀ w, hcell w p i -∗ harray (L.set (Int.natAbs i) w) p) := by
  move=> [] *
  srw ?harray ; xchange (hseg_focus i) ; omega ; simp
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

lemma triple_array_length_hheader (n : Int) (p : loc) :
  triple (trm_app val_array_length p)
    (hheader n p)
    (fun r ↦ ⌜r = n⌝ ∗ hheader n p) := by
    xwp
    srw hheader
    sorry

lemma triple_array_get_hcell (p : loc) (i : Int) (v : val) :
  triple (trm_app val_array_get p i)
    (hcell v p i)
    (fun r ↦ ⌜r = v⌝ ∗ hcell v p i) := by
    xwp
    srw hcell val_array_get
    xpull
    sorry

lemma triple_array_set_hcell (p : loc) (i : Int) (v w : val) :
  triple (trm_app val_array_set p i v)
    (hcell w p i)
    (fun _ ↦ hcell v p i) := by
    xwp
    srw hcell val_array_set
    xpull
    sorry

lemma triple_array_get_hseg L (p : loc) (i j : Int) :
  0 <= i - j ∧ i - j < L.length →
  triple (trm_app val_array_get p i)
    (hseg L p j)
    (fun r ↦ ⌜r = L[Int.natAbs (i - j)]!⌝ ∗ hseg L p j) := by
    move=> ?
    xtriple
    xchange (hseg_focus i)=>//
    xapp triple_array_get_hcell
    xchange (hforall_specialize)
    srw set_nth_same ; xsimp ; omega

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
    { sorry }
    sorry }
  sdone

lemma triple_array_make_hseg (n : Int) (v : val) :
  n >= 0 →
  triple (trm_app val_array_make n v)
    emp
    (funloc p ↦ hheader (Int.natAbs n) p ∗ hseg (make_list (Int.natAbs n) v) p 0) := by
  srw val_array_make=> ?
  xwp
  sorry

lemma triple_array_get L (p : loc) (i : Int) :
   0 <= i ∧ i < L.length →
   triple (trm_app val_array_get p i)
    (harray L p)
    (fun r ↦ ⌜r = L[Int.natAbs i]!⌝ ∗ harray L p) := by
    move=> ?
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
  sby srw make_list_len
