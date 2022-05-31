(* Permutations based on Pmap from std++. *)

Require Import PArith.
From stdpp Require Import base option list numbers pmap.

Global Open Scope positive_scope.
Global Open Scope list_scope.

Definition perm_lookup_raw (m : Pmap positive) (i : positive) : positive :=
  default i (m !! i).

Definition perm_compose_raw (m1 m2 : Pmap positive) : Pmap positive :=
  merge (from_option Some) m2 (perm_lookup_raw m2 <$> m1).

Lemma contra {P Q : Prop} :
  (P -> Q) -> ¬ Q -> ¬ P.
Proof. auto. Qed.

Lemma perm_compose_raw_inj (m1 m2 : Pmap positive) :
  Inj eq eq (perm_lookup_raw m1) ->
  Inj eq eq (perm_lookup_raw m2) ->
  Inj eq eq (perm_lookup_raw (perm_compose_raw m1 m2)).
Proof.
intros H1 H2 x1 x2; repeat unfold perm_lookup_raw, perm_compose_raw in *.
rewrite ?lookup_merge, ?lookup_fmap; intros H3.
destruct (decide (x1 = x2)) as [H4|H4]; [done|exfalso].
assert (H5 := contra (H1 _ _) H4); cbn in *;
repeat destruct (m1 !! _); cbn in *;
assert (H6 := contra (H2 _ _) H5); cbn in *;
repeat destruct (m2 !! _); done.
Qed.

Lemma perm_compose_raw_surj (m1 m2 : Pmap positive) :
  Surj eq (perm_lookup_raw m1) ->
  Surj eq (perm_lookup_raw m2) ->
  Surj eq (perm_lookup_raw (perm_compose_raw m1 m2)).
Proof.
intros H1 H2 z; destruct (H2 z) as [y Hy], (H1 y) as [x Hx]; exists x.
clear H1 H2; unfold perm_lookup_raw, perm_compose_raw in *.
rewrite lookup_merge, lookup_fmap; simplify_option_eq.
destruct (m1 !! x) as [y|]; cbn. unfold perm_lookup_raw.
destruct (m2 !! x), (m2 !! y); done. destruct (m2 !! x); done.
Qed.

Inductive perm := Perm {
  perm_car  : Pmap positive;
  perm_inj  : Inj eq eq (perm_lookup_raw perm_car);
  perm_surj : Surj eq (perm_lookup_raw perm_car);
}.

Definition perm_compose (π τ : perm) :=
  let (π_m, π_inj, π_surj) := π in
  let (τ_m, τ_inj, τ_surj) := τ in
  Perm (perm_compose_raw π_m τ_m)
    (perm_compose_raw_inj _ _ π_inj τ_inj)
    (perm_compose_raw_surj _ _ π_surj τ_surj).

Notation perm_lookup π := (perm_lookup_raw (perm_car π)).
Notation "π ⋅ i" := (perm_lookup π i) (at level 5, format "π ⋅ i").
Notation "π ∘ τ" := (perm_compose π τ).
