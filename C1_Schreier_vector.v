(* A functional Schreier-vector to compute orbits. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word B4_group.

Module Schreier.
Section Vector.

Definition vector := fmap perm.

(* Add all numbers reachable from i. *)
Fixpoint extend (i : positive) (h : perm)
  (gen : list perm) (V : vector)
  (acc : list positive) :=
  match gen with
  | [] => (V, acc)
  | g :: gen' =>
    let j := g⋅i in
    match lookup V j with
    | Some _ => extend i h gen' V acc
    | None => extend i h gen' (insert V j (g ∘ h)) (j :: acc)
    end
  end.

(* The generating set. *)
Variable gen : list perm.

(* Extend all numbers in the try list. *)
Fixpoint extend_loop (V : vector) (try acc : list positive) :=
  match try with
  | [] => (V, acc)
  | i :: try' =>
    match lookup V i with
    | None => extend_loop V try' acc
    | Some h =>
      match extend i h gen V acc with
      | (V', acc') => extend_loop V' try' acc'
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
    | (V', try') => loop V' try' m
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

Lemma sound_extend h gen' V acc :
  Generates gen h -> gen' ⊆ gen ->
  Sound V -> Sound (fst (extend h⋅k h gen' V acc)).
Proof.
revert V acc; simple_ind gen'.
apply incl_cons_inv in H0 as [].
destruct (lookup _); apply IHgen'; try easy.
intros j; rewrite lookup_insert.
destruct (_ =? _) eqn:E; [convert_bool; subst; split|apply H1].
apply compose_generator; easy. apply apply_compose.
Qed.

Lemma sound_extend_loop V try acc :
  Sound V -> Sound (fst (extend_loop V try acc)).
Proof.
revert V acc; simple_ind try.
destruct (lookup V a) eqn:E. destruct (extend _) as [V' acc'] eqn:E'.
replace V' with (fst (extend a p gen V acc)) by (rewrite E'; easy).
all: apply IHtry. assert(Ha := H a); rewrite E in Ha; destruct Ha; subst.
apply sound_extend; easy. easy.
Qed.

Lemma sound_loop V try n :
  Sound V -> Sound (loop V try n).
Proof.
revert V try; simple_ind n.
destruct (extend_loop _) as [V' try'] eqn:E.
replace V' with (fst (extend_loop V try [])) by (rewrite E; easy).
destruct try'. apply sound_extend_loop, H.
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

Lemma complete_extend_loop_keep V try acc i :
  Contains V i -> Contains (fst (extend_loop V try acc)) i.
Proof.
Admitted.

Lemma complete_loop_keep V try n i :
  Contains V i -> Contains (loop V try n) i.
Proof.
Admitted.

Lemma complete_extend_loop_add V try acc V' try' σ i:
  In σ gen -> In i try ->
  extend_loop V try acc = (V', try') ->
  ¬Contains V σ⋅i -> Contains V' σ⋅i /\ In σ⋅i try'.
Proof.
Admitted.

Lemma complete_loop V try n i w :
  w ⊆ gen -> length w <= n -> In i try ->
  Contains V i -> Contains (loop V try n) (apply' w i).
Proof.
revert V try i w; induction n; simpl; intros.
destruct w; easy. destruct (extend_loop _) as [V' try'] eqn:E.
destruct w as [|σ w]; simpl.
- (* The orbit point is already found. *)
  assert(Contains V' i).
  replace V' with (fst (extend_loop V try [])).
  apply complete_extend_loop_keep, H2. rewrite E; easy.
  destruct try'. apply H3. apply complete_loop_keep, H3.
- (* We can apply an induction step. *)
  (* Problem: what if σ⋅i is already contained in V? *)
  (* Do we have to search w for a continuation point? *)
Admitted.

Theorem complete_build n :
  size (union_range gen) <= n -> Complete (build n).
Proof.
intros H π [w []]; unfold build.
destruct (short_connecting_word w k) as [w' [? []]].
rewrite H1, apply_compose', <-H4. apply complete_loop.
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
