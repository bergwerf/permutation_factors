(* Verification of the Schreier-Sims subgroup chain algorithm. *)

From permlib Require Import perm order Schreier_Sims.

Arguments singletonM : simpl never.

Module Schreier.
Import Schreier.
Section Vector.

Variable k : positive.
Variable gen : list perm.
Notation build := (build gen k).
Notation build_step := (build_step gen).
Notation generators := (generators gen k).

Definition Sound (orb : orbit) :=
  ∀ i π, orb !! i = Some π -> Generates gen π ∧ π !!! k = i.

Definition Complete (orb : orbit) :=
  ∀ π, Generates gen π -> is_Some (orb !! (π !!! k)).

Definition Value_Bound (π : perm) (n : positive) :=
  ∀ i, π !!! i ≠ i -> π !!! i ≤ n.

Implicit Types s : state.
Implicit Types orb : orbit.
Implicit Types cur : list (positive * perm).
Implicit Types p : positive * perm.

Section Soundness.

Lemma iterate_invariant {X} (P : X -> Prop) n f x :
  P x -> (∀ y, P y -> P (f y)) -> P (iterate n f x).
Proof.
revert x; induction n; firstorder.
Qed.

Lemma foldl_invariant {A B} (P : B -> Prop) (f : B -> A -> B) l :
  (∀ a b, a ∈ l -> P b -> P (f b a)) -> ∀ b0, P b0 -> P (foldl f b0 l).
Proof.
intros Hf; induction l; intros b0 H0; cbn. done.
apply IHl; intros; apply Hf; auto; apply elem_of_cons; tauto.
Qed.

Definition Sound_State (s : state) :=
  Sound s.1 ∧ ∀ i π, (i, π) ∈ s.2 -> s.1 !! i = Some π.

Theorem build_sound n :
  Sound_State (build n).
Proof.
unfold build; apply iterate_invariant.
- split; intros i π; cbn; intros.
  + apply lookup_singleton_Some in H as [-> <-]; split.
    apply generates_e. done.
  + apply elem_of_list_singleton in H; injection H; intros -> ->.
    apply lookup_insert.
- intros [orb cur]; cbn; intros Horb.
  apply foldl_invariant. intros [i π] [orb' cur'] H1 H2; cbn.
  apply foldl_invariant. intros σ [orb'' cur''] H3 H4; cbn.
  3: firstorder; list_simplifier; decompose_elem_of_list.
  2: firstorder. destruct (_ !! _) eqn:Hi; cbn. tauto.
  split; intros j τ; cbn; intros Hj.
  + apply lookup_insert_Some in Hj as [[<- <-]|[]]; [|firstorder].
    apply Horb, Horb in H1 as [Hπ Hk]; split.
    apply generates_compose. done. apply generates_generator; done.
    rewrite lookup_compose; congruence.
  + apply elem_of_cons in Hj as [].
    injection H; intros <- <-; apply lookup_insert.
    apply H4 in H; cbn in H; etrans; [apply lookup_insert_ne|].
    congruence. done.
Qed.

End Soundness.

Section Completeness.

Lemma build_step_complete w s :
  w ⊆ gen ++ (inv <$> gen) ->
  let (orb, _) := iterate (length w) build_step s in
  is_Some (orb !! (comp w !!! k)).
Proof.
induction w; intros; cbn.
(* We have to determine the right pre-condition for the list of current indices.
Each index from which new indices are reachable must be present. *)
Admitted.

Variable n : positive.
Hypothesis exhaustive : ∀ π, π ∈ gen -> Value_Bound π n.

Lemma build_complete :
  Complete (build (Pos.to_nat n)).1.
Proof.
intros _ [w [? ->]].
(* We need the Pigeon-Hole-Principle to show that a prefix of w with length at
most n has the same value at k, so we can apply build_step_complete. *)
Admitted.

End Completeness.

Section Schreiers_lemma.

Variable orb : orbit.
Hypothesis sound : Sound orb.
Hypothesis complete : Complete orb.

Lemma generators_sound_1 :
  Forall (Generates gen) (generators orb).
Proof.
Admitted.

Lemma generators_sound_2 π :
  Generates (generators orb) π -> π !!! k = k.
Proof.
Admitted.

Lemma generators_complete π :
  Generates gen π -> π !!! k = k -> Generates (generators orb) π.
Proof.
Admitted.

End Schreiers_lemma.

End Vector.
End Schreier.

Module Sims.
Import Sims.
Section Filter.

Variable n : nat.
Notation filter := (filter n).

Lemma filter_sound gen π :
  Generates (values (filter gen)) π -> Generates gen π.
Proof.
Admitted.

Lemma filter_complete gen π :
  Generates gen π -> Generates (values (filter gen)) π.
Proof.
Admitted.

End Filter.
End Sims.

Module SGChain.
Import SGChain.
Section Order.

Variable gen : list perm.
Variable ks : list positive.

Hypothesis ks_complete : ∀ k π, π ∈ gen ∧ π !!! k ≠ k -> k ∈ ks.

Theorem order_spec :
  Group_Order gen (order (build gen ks)).
Proof.
Admitted.

End Order.
End SGChain.
