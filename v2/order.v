(* The order of a permutation group given a generating set. *)

From stdpp Require Import finite.
From permlib Require Import perm.

Notation comp := (foldr (⋅) ∅).

Arguments reverse _ : simpl never.

Local Ltac simpl_elem_of :=
  repeat match goal with
  | H : ?x ∈ ?f <$> ?l |- _ =>
    let y := fresh x in
    apply elem_of_list_fmap in H as (y & -> & H);
    rename y into x
  end.

Theorem perm_order (π : perm) :
  ∃ n, comp (repeat π (S n)) ≡ ∅.
Proof.
Admitted.

Section Generating_set.

Variable gen : list perm.

Definition Generates (π : perm) :=
  ∃ w, w ⊆ gen ∧ π ≡ comp w.

Record Group_Order (ord : positive) := Group_Enumeration {
  enum : positive -> perm;
  enum_gen : ∀ i, i ≤ ord -> Generates (enum i);
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
exists [σ]; split; cbn. set_solver.
symmetry; apply (right_id ∅ (⋅)).
Qed.

Lemma comp_app w1 w2 :
  comp (w2 ++ w1) ≡ comp w2 ⋅ comp w1.
Proof.
induction w2; cbn; intros; symmetry.
apply (left_id ∅ (⋅)). rewrite <-(assoc (⋅)), IHw2; done.
Qed.

Lemma generates_compose τ π :
  Generates τ -> Generates π -> Generates (π⋅τ).
Proof.
intros [w_τ [H1 H2]] [w_π [H3 H4]]; exists (w_π ++ w_τ); split.
set_solver. rewrite comp_app, H2, H4; done.
Qed.

Lemma generates_inv π :
  Generates π -> Generates (inv π).
Proof.
intros [w [H1 H2]]; destruct (perm_order π) as [n H3]; cbn in H3.
exists (concat (repeat w n)); split.
- clear H2 H3; induction n; cbn; set_solver.
- assert(H4 : inv π ≡ comp (repeat π n)).
  + symmetry; rewrite <-(left_id ∅ (⋅)), <-(left_inv π) at 1.
    rewrite <-(assoc (⋅)), H3, (right_id ∅ (⋅)); done.
  + rewrite H4; clear H1 H3 H4; induction n; cbn in *. done.
    rewrite IHn; rewrite H2, comp_app; done.
Qed.

End Generating_set.

Lemma unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ∅); intros. apply generates_e. lia. destruct H as [w []].
apply list_nil_subseteq in H as ->; exists 1; done.
Qed.
