(* A functional Schreier-vector to compute orbits. *)

From Permutations Require Import A_setup B1_finite_map B2_permutation.

Module Schreier.

Definition vector := fmap perm.

Section Algorithm.

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

Variable generator : list perm.

(* Extend all numbers in the try list. *)
Fixpoint extend_loop (V : vector) (try acc : list positive) :=
  match try with
  | [] => (V, acc)
  | i :: try' =>
    match lookup V i with
    | None => extend_loop V try' acc
    | Some h =>
      match extend i h generator V acc with
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

(* Build a full orbit vector for a given permutation range. *)
Definition build (range : nat) (k : positive) :=
  loop (insert Leaf k ident) [k] range.

End Algorithm.

End Schreier.
