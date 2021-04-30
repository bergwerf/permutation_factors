(* A functional Sims-filter to reduce generator sets. *)

From Permutations Require Import A_setup B1_finite_map B2_permutation.

Module Sims.

Definition filter := fmap (fmap perm).

Section Algorithm.

(* Find the smallest mapping in π. *)
Fixpoint min (π : perm) : option (positive × positive) :=
  match π with
  | Leaf => None
  | Node (Some j) _ _ => Some (xH, j)
  | Node None πO πI =>
    match min πO, min πI with
    | None, None => None
    | None, Some (i, j) => Some (i~0, j)
    | Some (i, j), None => Some (i~1, j)
    | Some (i, j), Some (i', j') =>
      Some (if i <? i' then (i~0, j) else (i'~1, j'))
    end
  end.

Variable sieve : perm.

(* Add g to the filter or discard it. *)
Fixpoint crack (F : filter) (range : nat) (g : perm) :=
  match range with
  | O => F
  | S ran =>
    let g' := sift g sieve in
    match min g' with
    | None => F
    | Some (i, j) =>
      match lookup F i with
      | None => insert F i (create j g')
      | Some Fi =>
        match lookup Fi j with
        | None => insert F i (insert Fi j g')
        | Some h => crack F ran (inv g ∘ h)
        end
      end
    end
  end.

Variable range : nat.

Fixpoint loop (gen : list perm) (F : filter) :=
  match gen with
  | [] => F
  | g :: gen' => loop gen' (crack F range g)
  end.

Definition percolate (gen : list perm) :=
  flat_map values (values (loop gen Leaf)).

End Algorithm.

End Sims.
