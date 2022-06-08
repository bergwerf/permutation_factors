(* The order of a permutation group given a generating set. *)

From permlib Require Import perm.

Arguments reverse _ : simpl never.

Local Ltac simpl_elem_of :=
  repeat match goal with
  | H : ?x ∈ ?f <$> ?l |- _ =>
    let y := fresh x in
    apply elem_of_list_fmap in H as (y & -> & H);
    rename y into x
  end.

Section Generating_set.

Variable gen : list perm.

Definition Generates (π : perm) :=
  ∃ w, w ⊆ gen ++ (inv <$> gen) ∧ π ≡ foldr (⋅) ∅ w.

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
exists [σ]; split.
- intros a Ha; apply elem_of_app; left.
  decompose_elem_of_list; subst; done.
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

Lemma foldr_ext_1 `{Group X f i e} (x y : X) l :
  x ≡ y -> foldr f x l ≡ foldr f y l.
Proof.
induction l; cbn; intros.
done. rewrite IHl; done.
Qed.

Lemma foldr_propagate `{Group X f i e} (x y : X) l :
  foldr f (f x y) l ≡ f (foldr f x l) y.
Proof.
induction l; cbn. done.
rewrite IHl, (assoc f); done.
Qed.

Lemma convert_word σs w' :
  (∀ σ', σ' ∈ w' -> ∃ σ, σ ∈ σs ∧ σ ≡ σ') ->
  ∃ w, w ⊆ σs ∧ foldr (⋅) ∅ w ≡ foldr (⋅) ∅ w'.
Proof.
induction w'; cbn; intros H.
- exists []; cbn; split. apply list_subseteq_nil. done.
- destruct (H a) as [σ []]; [constructor|].
  destruct IHw' as [w []]; [set_solver|exists (σ :: w)].
  split; [set_solver|cbn]; solve_proper.
Qed.

Lemma generates_inv π :
  Generates π -> Generates (inv π).
Proof.
pose (σs := gen ++ (inv <$> gen)); intros (w & H1 & H2).
destruct (convert_word σs (inv <$> reverse w)) as [w' []]; unfold σs in *.
- intros; simpl_elem_of; apply (elem_of_reverse _ w), H1 in H.
  decompose_elem_of_list; simpl_elem_of.
  + exists (inv σ'); split; [set_solver|done].
  + exists σ'; split; [set_solver|symmetry; apply inv_inv].
- exists w'; split; [done|]; rewrite H2; etrans; [|done]; clear.
  induction w; cbn; [done|]; rewrite inv_compose, IHw.
  rewrite reverse_cons, fmap_app, foldr_app; etrans; [|eapply foldr_ext_1]; cbn.
  rewrite foldr_propagate; done. rewrite (left_id ∅ _), (right_id ∅ _); done.
Qed.

End Generating_set.

Lemma unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ∅); intros. apply generates_e. lia. destruct H as [w []].
apply list_nil_subseteq in H as ->; exists 1; done.
Qed.
