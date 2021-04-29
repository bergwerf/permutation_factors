(* A functional Schreier-vector to compute orbits. *)

From permutation_solver Require Import A_setup B1_finite_map B2_permutation.

Module Schreier.

Definition vector := fmap perm.

Section Algorithm.

Fixpoint step (i : positive) (π : perm)
  (gen : list perm) (V : vector)
  (acc : list positive) :=
  match gen with
  | [] => (V, acc)
  | σ :: gen' =>
    let j := σ⋅i in
    match lookup V j with
    | Some _ => step i π gen' V acc
    | None => step i π gen' (insert V j (σ ∘ π)) (j :: acc)
    end
  end.

Variable generator : list perm.

Fixpoint cycle (V : vector) (try acc : list positive) :=
  match try with
  | [] => (V, acc)
  | i :: try' =>
    match lookup V i with
    | Some π =>
      match step i π generator V acc with
      | (V', acc') => cycle V' try' acc'
      end
    | None => cycle V try' acc
    end
  end.

Fixpoint iterate (V : vector) (try : list positive) (n : nat) :=
  match n with
  | O => V
  | S m =>
    match cycle V try [] with
    | (V', []) => V'
    | (V', try') => iterate V' try' m
    end
  end.

Definition build (size k : positive) :=
  iterate (insert Leaf k ident) [k] (Pos.to_nat size).

End Algorithm.

End Schreier.
