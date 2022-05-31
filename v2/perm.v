(* Permutations based on Pmap from std++. *)

Require Import DecimalString.
From stdpp Require Import strings.
From stdpp Require Export base numbers option list pmap.

Global Open Scope positive_scope.
Global Open Scope list_scope.

Definition pmap_f (m : Pmap positive) (i : positive) : positive :=
  default i (m !! i).

Definition pmap_swap (i j : positive) : Pmap positive :=
  {[i:=j; j:=i]}.

Definition pmap_compose (m1 m2 : Pmap positive) : Pmap positive :=
  merge (from_option Some) m2 (pmap_f m2 <$> m1).

Lemma contra {P Q : Prop} :
  (P -> Q) -> ¬ Q -> ¬ P.
Proof. auto. Qed.

Lemma pmap_empty_inj :
  Inj eq eq (pmap_f ∅).
Proof.
Admitted.

Lemma pmap_empty_surj :
  Surj eq (pmap_f ∅).
Proof.
Admitted.

Lemma pmap_swap_inj i j :
  Inj eq eq (pmap_f (pmap_swap i j)).
Proof.
Admitted.

Lemma pmap_swap_surj i j :
  Surj eq (pmap_f (pmap_swap i j)).
Proof.
Admitted.

Lemma pmap_compose_inj (m1 m2 : Pmap positive) :
  Inj eq eq (pmap_f m1) ->
  Inj eq eq (pmap_f m2) ->
  Inj eq eq (pmap_f (pmap_compose m1 m2)).
Proof.
intros H1 H2 x1 x2; repeat unfold pmap_f, pmap_compose in *.
rewrite ?lookup_merge, ?lookup_fmap; intros H3.
destruct (decide (x1 = x2)) as [H4|H4]; [done|exfalso].
assert (H5 := contra (H1 _ _) H4); cbn in *;
repeat destruct (m1 !! _); cbn in *;
assert (H6 := contra (H2 _ _) H5); cbn in *;
repeat destruct (m2 !! _); done.
Qed.

Lemma pmap_compose_surj (m1 m2 : Pmap positive) :
  Surj eq (pmap_f m1) ->
  Surj eq (pmap_f m2) ->
  Surj eq (pmap_f (pmap_compose m1 m2)).
Proof.
intros H1 H2 z; destruct (H2 z) as [y Hy], (H1 y) as [x Hx]; exists x.
clear H1 H2; unfold pmap_f, pmap_compose in *.
rewrite lookup_merge, lookup_fmap; simplify_option_eq.
destruct (m1 !! x) as [y|]; cbn; unfold pmap_f.
destruct (m2 !! x), (m2 !! y); done.
destruct (m2 !! x); done.
Qed.

Inductive perm := Perm {
  perm_car  : Pmap positive;
  perm_inj  : Inj eq eq (pmap_f perm_car);
  perm_surj : Surj eq (pmap_f perm_car);
}.

Global Instance : FinMapToList positive positive perm :=
  λ π, map_to_list (perm_car π).

Global Instance perm_lookup : LookupTotal positive positive perm :=
  λ i π, pmap_f (perm_car π) i.

Global Instance : Empty perm :=
  Perm _ pmap_empty_inj pmap_empty_surj.

Definition perm_swap (i j : positive) :=
  Perm _ (pmap_swap_inj i j) (pmap_swap_surj i j).

Definition perm_compose (π τ : perm) :=
  let (π_m, π_inj, π_surj) := π in
  let (τ_m, τ_inj, τ_surj) := τ in
  Perm (pmap_compose π_m τ_m)
    (pmap_compose_inj _ _ π_inj τ_inj)
    (pmap_compose_surj _ _ π_surj τ_surj).

Notation "⟨ i ; j ⟩" := (perm_swap i j) (format "⟨ i ;  j ⟩").
Notation "π ⋅ τ" := (perm_compose τ π) (at level 15).

Definition perm_cycle (i : positive) (is : list positive) : perm :=
  foldl (λ π j, ⟨i; j⟩ ⋅ π) ∅ is.

Notation "⟨ i ; x ; y ; .. ; z ⟩" :=
  (perm_cycle i (cons x (cons y .. (cons z nil) ..)))
  (format "⟨ i ;  x ;  y ;  .. ;  z ⟩").

Theorem lookup_compose π τ i :
  π ⋅ τ !!! i = π !!! (τ !!! i).
Proof.
destruct τ as [τ_m ? ?], π as [π_m ? ?]; unfold lookup_total, perm_lookup; cbn.
unfold pmap_f, pmap_compose; rewrite lookup_merge, lookup_fmap.
destruct (τ_m !! i) as [i1|]; cbn; unfold pmap_f.
destruct (π_m !! i) as [i0|], (π_m !! i1); done.
destruct (π_m !! i) as [i0|]; done.
Qed.

Section Printing.

Definition cycle := list positive.

(* Append a cycle segment to a list of cycles. *)
Fixpoint cycles_add (cycles : list (positive * cycle * positive))
  (i0 : positive) (is : cycle) (ik : positive) :=
  match cycles with
  | [] => [(i0, is, ik)]
  | (j0, js, jk) :: cs =>
    if decide (ik = j0)
    then cycles_add cs i0 (is ++ [ik] ++ js) jk
    else if decide (i0 = jk)
    then cycles_add cs j0 (js ++ [i0] ++ is) ik
    else (j0, js, jk) :: cycles_add cs i0 is ik
  end.

(* Convert a permutation to a list of cycles. *)
Definition perm_cycles (π : perm) : list cycle :=
  (λ c, match c with (i0, is, ik) => i0 :: is ++ [ik] end) <$>
  (foldl (λ cs m, match m with (i, j) =>
    if decide (i = j) then cs
    else cycles_add cs i [] j end)
    [] (map_to_list π)).

Fixpoint str_join (sep : string) (l : list string) :=
  match l with
  | [] => ""
  | [x] => x
  | x :: l' => x +:+ sep +:+ str_join sep l'
  end.

Definition str_of_pos i :=
  NilZero.string_of_uint (Pos.to_uint i).

Definition str_of_cycle (c : cycle) :=
  "(" +:+ str_join " " (map str_of_pos (removelast c)) +:+ ")".

Definition str_of_perm (π : perm) :=
  str_join "" (str_of_cycle <$> perm_cycles π).

End Printing.
