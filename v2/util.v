(* Utilities based on std++. *)

From stdpp Require Export base numbers option list fin_maps.

Ltac simpl_lookup :=
  repeat match goal with
  | H : {[_:=_]} !! _ = Some _ |- _ =>
    apply lookup_singleton_Some in H as []
  | H : <[_:=_]> _ !! _ = Some _ |- _ =>
    apply lookup_insert_Some in H as [[]|[]]; subst
  | H : delete _ _ !! _ = Some _ |- _ =>
    apply lookup_delete_Some in H as []
  end.

Ltac simpl_elem_of :=
  repeat match goal with
  | H : (?x, ?y) ∈ map_to_list _ |- _ =>
    apply elem_of_map_to_list in H
  | H : ?x ∈ map_to_list _ |- _ =>
    destruct x
  | H : (?x, ?y) ∈ ?f <$> ?l |- _ =>
    apply elem_of_list_fmap in H as ([] & ? & H)
  | H : ?x ∈ ?f <$> ?l |- _ =>
    let y := fresh x in
    apply elem_of_list_fmap in H as (y & -> & H);
    rename y into x
  end.

Lemma list_difference_nil `{dec : EqDecision A} (l k : list A) :
  l ⊆ k -> list_difference l k = [].
Proof.
induction l; cbn; intros. done.
destruct decide_rel; set_solver.
Qed.

Lemma list_union_cancel `{dec : EqDecision A} (l k : list A) :
  l ⊆ k -> list_union l k = k.
Proof.
intros; unfold list_union;
rewrite list_difference_nil; done.
Qed.

Lemma list_union_sym `{dec : EqDecision A} (l k : list A) :
  NoDup l -> NoDup k -> list_union l k ≡ₚ list_union k l.
Proof.
Admitted.
