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

Theorem generates_ident :
  Generates ident.
Proof.
exists []; easy.
Qed.

Theorem generates_generator σ :
  In σ gen -> Generates σ.
Proof.
exists [σ]; split. auto with datatypes.
intros i; simpl; rewrite apply_compose; easy.
Qed.

Theorem generates_subst π τ :
  τ == π -> Generates π -> Generates τ.
Proof.
intros ? [w []]; exists w; split. easy.
etransitivity. apply H. easy.
Qed.

Theorem generates_compose π τ :
  Generates π -> Generates τ -> Generates (τ ∘ π).
Proof.
intros [w []] [w' []]; exists (w ++ w'); split.
auto with datatypes. rewrite fold_right_app.
intros i; rewrite compose''_compose', ?apply_compose, <-H0, <-H2; easy.
Qed.

Theorem generates_inv π :
  Generates π -> Generates (inv π).
Proof.
Admitted.

End Groups.

Theorem unit_group_order :
  Group_Order [] 1.
Proof.
exists (λ _, ident); repeat split; intros. destruct H as [w []].
apply incl_l_nil in H; subst; simpl in H0. exists 1; easy. lia.
Defined.
