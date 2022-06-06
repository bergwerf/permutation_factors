(* Verification of the Schreier-Sims subgroup chain algorithm. *)

From permlib Require Import perm order Schreier_Sims.

Module Schreier.
Import Schreier.
Section Vector.

Variable k : positive.
Variable gen : list perm.
Notation build := (build gen k).
Notation generators := (generators gen k).

Definition Sound (orb : orbit) :=
  ∀ i π, orb !! i = Some π -> Generates gen π ∧ π !!! k = i.

Definition Complete (orb : orbit) :=
  ∀ π, Generates gen π -> is_Some (orb !! (π !!! k)).

Definition ImageBound (π : perm) (n : positive) :=
  ∀ i, π !!! i ≠ i -> π !!! i ≤ n.

Section Soundness.

Lemma build_sound n :
  Sound (build n).1.
Proof.
Admitted.

End Soundness.

Section Completeness.

Variable n : positive.
Hypothesis exhaustive : ∀ π, π ∈ gen -> ImageBound π n.

Lemma build_complete :
  Complete (build n).1.
Proof.
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
