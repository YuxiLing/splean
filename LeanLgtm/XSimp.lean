import SSReflect.Lang
import LeanLgtm.Basic


/-
Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 ->
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.
-/
lemma himpl_of_eq H1 H2 : H1 = H2 -> H1 ==> H2 :=
  by sby move=>-> ?

lemma himpl_of_eq_sym H1 H2  : H1 = H2 -> H2 ==> H1 :=
  by sby move=>-> ?
