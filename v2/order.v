(* The order of a permutation group given a generating set. *)

From permlib Require Import perm.

Section Generating_set.

Variable gen : list perm.

Definition Generates (π : perm) :=
  ∃ w, w ⊆ gen ∧ π ≡ foldr (⋅) ∅ w.

Record Group_Order (ord : positive) := Group_Enumeration {
  enum : positive -> perm;
  enum_inj : ∀ i j, i ≤ ord -> j ≤ ord -> enum i ≡ enum j -> i = j;
  enum_surj : ∀ π, Generates π -> ∃ i, i ≤ ord ∧ π ≡ enum i;
}.

End Generating_set.

Lemma unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ∅); intros. lia. destruct H as [w []].
apply list_nil_subseteq in H as ->; exists 1; done.
Qed.
