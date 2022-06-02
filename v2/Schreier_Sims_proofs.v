(* Verification of the Schreier-Sims subgroup chain algorithm. *)

From permlib Require Import perm order Schreier_Sims.

Module Schreier.
Import Schreier.
Section Vector.

Variable k : positive.
Variable gen : list perm.

Definition Sound (V : vector) :=
  ∀ i π, V !! i = Some π -> Generates gen π ∧ π !!! k = i.

Definition Complete (V : vector) :=
  ∀ π, Generates gen π -> is_Some (V !! (π !!! k)).

Definition ImageBound (π : perm) (n : positive) :=
  ∀ i, π !!! i ≠ i -> π !!! i ≤ n.

Variable V : vector.

Notation build := (build gen k).
Notation generators := (generators gen k).

Section Soundness.

Lemma build_sound bound :
  Sound (build bound).
Proof.
Admitted.

End Soundness.

Section Completeness.

Variable n : nat.
Hypothesis exhaustive : ∀ π, π ∈ gen -> ImageBound π (Pos.of_nat n).

Lemma build_complete :
  Complete (build n).
Proof.
Admitted.

End Completeness.

Section Schreiers_lemma.

Hypothesis sound : Sound V.
Hypothesis complete : Complete V.

Lemma generators_sound_1 :
  Forall (Generates gen) (generators V).
Proof.
Admitted.

Lemma generators_sound_2 π :
  Generates (generators V) π -> π !!! k = k.
Proof.
Admitted.

Lemma generators_complete π :
  Generates gen π -> π !!! k = k -> Generates (generators V) π.
Proof.
Admitted.

End Schreiers_lemma.

End Vector.
End Schreier.

Module Sims.
Import Sims.
Section Filter.

Variable range : nat.

Notation filter := (filter range).

Lemma filter_sound gen π :
  Generates (filter gen) π -> Generates gen π.
Proof.
Admitted.

Lemma filter_complete gen π :
  Generates gen π -> Generates (filter gen) π.
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
