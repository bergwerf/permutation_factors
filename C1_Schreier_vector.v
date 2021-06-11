(* A functional Schreier-vector to compute orbits. *)

From CGT Require Import A1_setup A2_lists B1_fmap B2_perm B3_word B4_group.

Module Schreier.
Section Vector.

Definition vector := fmap perm.

(* Add all numbers reachable from i. *)
Fixpoint extend (i : positive) (h : perm)
  (gen : list perm) (V : vector)
  (new : list positive) :=
  match gen with
  | [] => (V, new)
  | g :: gen' =>
    let j := g⋅i in
    match lookup V j with
    | Some _ => extend i h gen' V new
    | None => extend i h gen' (insert V j (g ∘ h)) (j :: new)
    end
  end.

(* The generating set. *)
Variable gen : list perm.

(* Extend all numbers in the source list. *)
Fixpoint extend_loop (V : vector) (try new : list positive) :=
  match try with
  | [] => (V, new)
  | i :: try' =>
    match lookup V i with
    | None => extend_loop V try' new
    | Some h =>
      match extend i h gen V new with
      | (V', new') => extend_loop V' try' new'
      end
    end
  end.

(* Repeat orbit extension n times. *)
Fixpoint loop (V : vector) (try : list positive) (n : nat) :=
  match n with
  | O => V
  | S m =>
    match extend_loop V try [] with
    | (V', []) => V'
    | (V', new) => loop V' new m
    end
  end.

(* The stabilizer point. *)
Variable k : positive.

(* Build an orbit vector given an orbit size bound. *)
(* Note that it doesn't make a difference if the bound is bigger than needed. *)
Definition build (bound : nat) := loop (insert Leaf k ident) [k] bound.

(* The orbit given by they keys of the Schreier vector. *)
Definition orbit (V : vector) : list positive := map fst (entries V xH).

(* The subgroup generators according to Schreier's Lemma. *)
Definition generators (V : vector) : list perm :=
  let ϕ := mapval inv V in map
  (λ a_u, let au := fst a_u ∘ snd a_u in (lookup ϕ au⋅k ?? ident) ∘ au)
  (list_prod gen (values V)).

(***
Theorems
*)

Section Soundness.

(* The orbit permutations are valid. *)
Definition Sound (V : vector) := ∀i,
  match lookup V i with
  | Some π => Generates gen π /\ π⋅k = i
  | None => True
  end.

Lemma sound_extend h gen' V new :
  Generates gen h -> gen' ⊆ gen ->
  Sound V -> Sound (fst (extend h⋅k h gen' V new)).
Proof.
revert V new; simple_ind gen'.
apply incl_cons_inv in H0 as [].
destruct (lookup _); apply IHgen'; try easy.
intros j; rewrite lookup_insert.
destruct (_ =? _) eqn:E; [convert_bool; subst; split|apply H1].
apply compose_generator; easy. apply apply_compose.
Qed.

Lemma sound_extend_loop V try new :
  Sound V -> Sound (fst (extend_loop V try new)).
Proof.
revert V new; simple_ind try.
destruct (lookup V a) eqn:E. destruct (extend _) as [V' new'] eqn:E'.
replace V' with (fst (extend a p gen V new)) by (rewrite E'; easy).
all: apply IHtry. assert(Ha := H a); rewrite E in Ha; destruct Ha; subst.
apply sound_extend; easy. easy.
Qed.

Lemma sound_loop V try n :
  Sound V -> Sound (loop V try n).
Proof.
revert V try; simple_ind n.
destruct (extend_loop _) as [V' new] eqn:E.
replace V' with (fst (extend_loop V try [])) by (rewrite E; easy).
destruct new. apply sound_extend_loop, H.
apply IHn, sound_extend_loop, H.
Qed.

Theorem sound_build bound :
  Sound (build bound).
Proof.
apply sound_loop.
intros i. rewrite lookup_insert; simpl.
destruct (k =? i) eqn:E. convert_bool; subst.
split. exists []; simpl; easy. easy. easy.
Qed.

End Soundness.

Section Completeness.

Local Open Scope nat.

(* The vector and the new points are an intermediary result. *)
Definition Intermediary (V : vector) new := Forall (λ i, Defined V i) new /\
  ∀i, Defined V i -> In i new \/ ∀σ, In σ gen -> Defined V σ⋅i.

(* The vector contains the full orbit. *)
Definition Complete (V : vector) :=
  ∀π, Generates gen π -> Defined V π⋅k.

Lemma defined_extend_loop V try new i :
  Defined V i -> Defined (fst (extend_loop V try new)) i.
Proof.
Admitted.

Lemma defined_loop V try m n i :
  Defined (loop V try m) i -> m <= n -> Defined (loop V try n) i.
Proof.
Admitted.

Lemma intermediary_extend_loop V try new V' try' :
  extend_loop V try new = (V', try') ->
  Intermediary V try -> Intermediary V' try'.
Proof.
Admitted.

Lemma defined_not_new V try new i :
  Defined V i -> ¬In i (snd (extend_loop V try new)).
Proof.
Admitted.

Lemma finished_intermediary V w i :
  Intermediary V [] -> Defined V i -> w ⊆ gen -> Defined V (apply' w i).
Proof.
intros [_ H]; revert i; simple_ind w.
apply incl_cons_inv in H1 as []. apply IHw.
apply H in H0 as []; [easy|apply H0, H1]. easy.
Qed.

Lemma complete_loop V try i w :
  w ⊆ gen -> Intermediary V try -> Defined V i ->
  Defined (loop V try (length w)) (apply' w i).
Proof.
revert V try i; induction w as [|σ w]; [easy|intros; simpl loop].
destruct (extend_loop _) as [V' new] eqn:E.
assert(Intermediary V' new). eapply intermediary_extend_loop; [apply E|easy].
eapply defined_extend_loop in H1 as H3; rewrite E in H3; simpl in H3.
eapply defined_not_new in H1 as H4; rewrite E in H4; simpl in H4.
destruct new as [|j new]. apply finished_intermediary; easy.
apply incl_cons_inv in H. simpl; apply IHw; try easy.
destruct H2 as [_ ?]; apply H2 in H3 as []; [easy|].
apply H3; easy.
Qed.

Theorem complete_build n :
  size (union_range gen) <= n -> Complete (build n).
Proof.
intros H π [w []]; unfold build.
destruct (short_connecting_word w k) as [w' [? []]].
assert(w' ⊆ gen) by eauto with datatypes.
rewrite H1, apply_compose', <-H4.
eapply defined_loop. apply complete_loop. easy.
- split. apply Forall_cons. rewrite lookup_insert_eq; easy. auto.
  intros. rewrite lookup_insert in H6.
  destruct (k =? i)%positive eqn:E; [|easy].
  convert_bool; subst; left; apply in_eq.
- rewrite lookup_insert_eq; easy.
- etransitivity; [|apply H]. rewrite size_eq_length_values.
  replace (length w') with (length (visited_points w' k)) at 1.
  apply NoDup_incl_length. easy. apply visited_points_range, H5.
  unfold visited_points; rewrite map_length, seq_length; easy.
Qed.

End Completeness.

Section Schreiers_lemma.

Variable V : vector.
Hypothesis sound : Sound V.
Hypothesis complete : Complete V.

Theorem generators_spec π :
  Generates gen π /\ π⋅k = k <-> Generates (generators V) π.
Proof.
Admitted.

End Schreiers_lemma.

End Vector.
End Schreier.
