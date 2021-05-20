(* Basic Group Theory definitions. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word.
Require Import Lia.

Section Group.

Notation can := (prune xH).
Notation Canonical := (Pruned xH).

(* The generating set of the group. *)
Variable gen : list perm.

(* Range of the generator after n compositions. *)
Fixpoint Generates n π :=
  match n with
  | O => can π = ident
  | S m => ∃σ, In σ gen /\ Generates m (σ ∘ π)
  end.

(* Group membership defined by the generator. *)
Definition In_Group π := ∃n, Generates n π.

(* Cardinality of the group. *)
Definition Group_Order (ord : positive) :=
  ∃f : positive -> perm,
    (∀i, i <= ord -> Canonical (f i)) /\
    (∀π, In_Group π -> ∃i, i <= ord /\ f i = can π) /\
    (∀i j, i <= ord -> j <= ord -> i ≠ j -> f i ≠ f j).

End Group.

Theorem unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ident); repeat split; intros.
2: lia. destruct H as [[]]; simpl in H.
exists 1; split; easy.
destruct H; easy.
Qed.
