(* A functional Schreier-vector to compute orbits. *)

From permutation_solver Require Import A_setup B1_finite_map B2_permutation.

Module Schreier.

Definition vector := fmap perm.

Section Algorithm.

Fixpoint extend (i : positive) (π : perm)
  (gen : list perm) (V : vector)
  (acc : list positive) :=
  match gen with
  | [] => (V, acc)
  | σ :: gen' =>
    let j := σ⋅i in
    match lookup V j with
    | Some _ => extend i π gen' V acc
    | None => extend i π gen' (insert V j (σ ∘ π)) (j :: acc)
    end
  end.

Variable generator : list perm.

Fixpoint step (V : vector) (try acc : list positive) :=
  match try with
  | [] => (V, acc)
  | i :: try' =>
    match lookup V i with
    | Some π =>
      match extend i π generator V acc with
      | (V', acc') => step V' try' acc'
      end
    | None => step V try' acc
    end
  end.

Fixpoint loop (V : vector) (try : list positive) (n : nat) :=
  match n with
  | O => V
  | S m =>
    match step V try [] with
    | (V', []) => V'
    | (V', try') => loop V' try' m
    end
  end.

Definition build (range k : positive) :=
  loop (insert Leaf k ident) [k] (Pos.to_nat range).

End Algorithm.

End Schreier.
