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

Lemma generates_e :
  Generates ∅.
Proof.
exists []; split; [|done].
apply list_subseteq_nil.
Qed.

Lemma generates_generator σ :
  σ ∈ gen -> Generates σ.
Proof.
exists [σ]; split.
- intros a Ha; decompose_elem_of_list; subst; done.
- symmetry; apply (right_id ∅ (⋅)).
Qed.

Lemma generates_compose τ π :
  Generates τ -> Generates π -> Generates (π⋅τ).
Proof.
intros [w_τ [H1 H2]] [w_π [H3 H4]]; exists (w_π ++ w_τ); split.
- intros a Ha; apply elem_of_app in Ha; firstorder.
- rewrite H2, H4; clear; induction w_π; cbn; intros.
  apply (left_id ∅ (⋅)). rewrite <-(assoc (⋅)), IHw_π; done.
Qed.

End Generating_set.

Lemma unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ∅); intros. lia. destruct H as [w []].
apply list_nil_subseteq in H as ->; exists 1; done.
Qed.
