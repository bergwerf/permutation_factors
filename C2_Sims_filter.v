(* A functional Sims-filter to reduce generating sets. *)

From CGT Require Import A1_setup B1_fmap B2_perm.

Module Sims.
Section Filter.

Definition table := fmap (fmap perm).

(* Find the smallest mapping in π. *)
Fixpoint minmap (π : perm) : option (positive × positive) :=
  match π with
  | Leaf => None
  | Node (Some j) _ _ => Some (xH, j)
  | Node None πO πI =>
    match minmap πO, minmap πI with
    | None, None => None
    | None, Some (i, j) => Some (i~0, j)
    | Some (i, j), None => Some (i~1, j)
    | Some (i, j), Some (i', j') =>
      Some (if i <? i' then (i~0, j) else (i'~1, j'))
    end
  end.

Variable sieve : perm.

(* Add g to the table or discard it. *)
Fixpoint crack (T : table) (range : nat) (g : perm) :=
  match range with
  | O => T
  | S ran =>
    let g' := sift sieve g in
    match minmap g' with
    | None => T
    | Some (i, j) =>
      match lookup T i with
      | None => insert T i (create j g')
      | Some Ti =>
        match lookup Ti j with
        | None => insert T i (insert Ti j g')
        | Some h => crack T ran (inv g ∘ h)
        end
      end
    end
  end.

Variable range : nat.

Fixpoint loop (gen : list perm) (T : table) :=
  match gen with
  | [] => T
  | g :: gen' => loop gen' (crack T range g)
  end.

Definition filter (gen : list perm) :=
  flat_map values (values (loop gen Leaf)).

End Filter.
End Sims.
