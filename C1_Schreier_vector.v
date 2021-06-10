(* A functional Schreier-vector to compute orbits. *)

From CGT Require Import A1_setup A2_lists B1_fmap B2_perm B3_word B4_group.

Module Schreier.
Section Vector.

Definition vector := fmap perm.

(* Add all numbers reachable from i. *)
Fixpoint extend (i : positive) (h : perm)
  (gen : list perm) (V : vector)
  (dst : list positive) :=
  match gen with
  | [] => (V, dst)
  | g :: gen' =>
    let j := g⋅i in
    match lookup V j with
    | Some _ => extend i h gen' V dst
    | None => extend i h gen' (insert V j (g ∘ h)) (j :: dst)
    end
  end.

(* The generating set. *)
Variable gen : list perm.

(* Extend all numbers in the source list. *)
Fixpoint extend_loop (V : vector) (src dst : list positive) :=
  match src with
  | [] => (V, dst)
  | i :: src' =>
    match lookup V i with
    | None => extend_loop V src' dst
    | Some h =>
      match extend i h gen V dst with
      | (V', dst') => extend_loop V' src' dst'
      end
    end
  end.

(* Repeat orbit extension n times. *)
Fixpoint loop (V : vector) (src : list positive) (n : nat) :=
  match n with
  | O => V
  | S m =>
    match extend_loop V src [] with
    | (V', []) => V'
    | (V', src') => loop V' src' m
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

Lemma sound_extend h gen' V dst :
  Generates gen h -> gen' ⊆ gen ->
  Sound V -> Sound (fst (extend h⋅k h gen' V dst)).
Proof.
revert V dst; simple_ind gen'.
apply incl_cons_inv in H0 as [].
destruct (lookup _); apply IHgen'; try easy.
intros j; rewrite lookup_insert.
destruct (_ =? _) eqn:E; [convert_bool; subst; split|apply H1].
apply compose_generator; easy. apply apply_compose.
Qed.

Lemma sound_extend_loop V src dst :
  Sound V -> Sound (fst (extend_loop V src dst)).
Proof.
revert V dst; simple_ind src.
destruct (lookup V a) eqn:E. destruct (extend _) as [V' dst'] eqn:E'.
replace V' with (fst (extend a p gen V dst)) by (rewrite E'; easy).
all: apply IHsrc. assert(Ha := H a); rewrite E in Ha; destruct Ha; subst.
apply sound_extend; easy. easy.
Qed.

Lemma sound_loop V src n :
  Sound V -> Sound (loop V src n).
Proof.
revert V src; simple_ind n.
destruct (extend_loop _) as [V' src'] eqn:E.
replace V' with (fst (extend_loop V src [])) by (rewrite E; easy).
destruct src'. apply sound_extend_loop, H.
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

(* The vector contains the full orbit. *)
Definition Complete (V : vector) := ∀π, Generates gen π -> Contains V π⋅k.

Lemma complete_extend_loop_keep V src dst i :
  Contains V i -> Contains (fst (extend_loop V src dst)) i.
Proof.
Admitted.

Lemma complete_loop_keep V src n i :
  Contains V i -> Contains (loop V src n) i.
Proof.
Admitted.

Lemma complete_extend_loop_add V src dst V' dst' σ i:
  In σ gen -> In i src ->
  extend_loop V src dst = (V', dst') ->
  ¬Contains V σ⋅i -> Contains V' σ⋅i /\ In σ⋅i dst'.
Proof.
Admitted.

Lemma complete_loop V src i w :
  w ⊆ gen -> In i src -> Contains V i ->
  Contains (loop V src (length w)) (apply' w i).
Proof.
apply rev_ind with (l:=w); clear w; [intros|intros σ w; intros]; simpl. easy.
apply incl_app_inv in H0 as []; apply H in H2; try easy; clear H0 H1.
Admitted.

Theorem complete_build n :
  size (union_range gen) <= n -> Complete (build n).
Proof.
intros H π [w []]; unfold build.
destruct (short_connecting_word w k) as [w' [? []]].
rewrite H1, apply_compose', <-H4.
Admitted.

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
