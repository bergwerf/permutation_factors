(* Basic Group Theory definitions. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word.
Require Import Lia.

(***
:: Groups ::

The Schreier-Sims algorithm describes groups, but we want to avoid proving more
Group Theory than strictly necessary. Therefore I favor short and efficient
definitions over more mathematically complete ones.
*)
Section Groups.

Notation can := (prune xH).
Notation Canonical := (Pruned xH).

(* The generating set of the group. *)
Variable gen : list perm.

(* Generator range for a bounded number of compositions. *)
Fixpoint Generates_in n π :=
  match n with
  | O => can π = ident
  | S m => ∃σ, In σ gen /\ Generates_in m (σ ∘ π)
  end.

(* Generator range for an unbounded number of compositions. *)
Definition Generates π := ∃n, Generates_in n π.

(* The number of distinct permutations that are generated. *)
Record Group_Order (ord : positive) := Group_Order_Witness {
  enum : positive -> perm;
  enum_canonical : ∀i, i <= ord -> Canonical (enum i);
  enum_surjective : ∀π, Generates π -> ∃i, i <= ord /\ enum i = can π;
  enum_injective : ∀i j, i <= ord -> j <= ord -> enum i = enum j -> i = j;
}.

End Groups.

Theorem unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ident); repeat split; intros.
destruct H as [[]]; simpl in H.
exists 1; split; easy.
destruct H; easy. lia.
Defined.
