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

(* The generating set. *)
Variable gen : list perm.

(* A permutation can be composed from the generating set. *)
Definition Generates π := ∃w, w ⊆ gen /\ π == compose' w.

(* The number of distinct permutations that are generated. *)
Record Group_Order (ord : positive) := Group_Order_Witness {
  enum : positive -> perm;
  enum_surjective : ∀π, Generates π -> ∃i, i <= ord /\ π == enum i;
  enum_injective : ∀i j, i <= ord -> j <= ord -> enum i == enum j -> i = j;
}.

(***
Theorems
*)

Theorem compose_generator σ π :
  Generates π -> In σ gen -> Generates (σ ∘ π).
Proof.
intros [w []] ?; exists (w ++ [σ]); split.
auto with incl. rewrite fold_left_app; simpl.
intros i; rewrite ?apply_compose, <-H0; easy.
Qed.

End Groups.

Theorem unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ident); repeat split; intros. destruct H as [w []].
apply incl_l_nil in H; subst; simpl in H0. exists 1; easy. lia.
Defined.
