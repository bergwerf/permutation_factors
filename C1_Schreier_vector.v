(* A functional Schreier-vector to compute orbits. *)

From CGT Require Import A1_setup B1_fmap B2_perm B4_group.

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

(* Build a full orbit vector for a given permutation range. *)
Definition build (range : nat) :=
  loop (insert Leaf k ident) [k] range.

(* The orbit given by they keys of the Schreier vector. *)
Definition orbit (V : vector) : list positive := map fst (entries V xH).

(* The subgroup generators according to Schreier's Lemma. *)
Definition generators (V : vector) : list perm := map
  (λ a_u, let au := fst a_u ∘ snd a_u in inv (lookup V au⋅k ?? ident) ∘ au)
  (list_prod gen (values V)).

(***
Theorems
*)

Section Schreiers_lemma.

Variable range : nat.
Hypothesis finished : ∀ran, (ran > range)%nat -> build ran = build range.

Theorem spec π :
  In_Group gen π /\ π⋅k = k <-> In_Group (generators (build range)) π.
Proof.
Admitted.

End Schreiers_lemma.

End Vector.
End Schreier.
