(* Utilities based on std++. *)

From stdpp Require Export base numbers option list fin_maps.
From stdpp Require Import pmap.

Global Open Scope positive_scope.
Global Open Scope list_scope.

Definition prod_swap {A} (p : A * A) :=
  match p with (x1, x2) => (x2, x1) end.

Definition keys `{FinMapToList K A M} (m : M) : list K :=
  (map_to_list m).*1.

Definition values `{FinMapToList K A M} (m : M) : list A :=
  (map_to_list m).*2.

Fixpoint pmap_keys {A} j (m : Pmap_raw A) : list positive :=
  match m with
  | PLeaf => []
  | PNode o l r =>
    (if o then [Preverse j] else []) ++
    pmap_keys j~0 l ++ pmap_keys j~1 r
  end.

Fixpoint Psuffix (s i : positive) :=
  match s, i with
  | 1, _ => True
  | t~0, j~0 => Psuffix t j
  | t~1, j~1 => Psuffix t j
  | _, _ => False
  end.

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

Ltac simpl_Permutation :=
  repeat match goal with
  | H : [] ≡ₚ _ |- _ =>
    symmetry in H
  | H : _ ≡ₚ [] |- _ =>
    apply Permutation_nil_r in H; try rewrite H
  end.

Global Instance prod_swap_inj {X} :
  Inj eq eq (@prod_swap X).
Proof.
intros [] []; cbn; congruence.
Qed.

Lemma NoDup_keys `{FinMap K M} {A} (m : M A) :
  NoDup (keys m).
Proof.
apply NoDup_fst_map_to_list.
Qed.

Lemma elem_of_keys `{FinMap K M} {A} (m : M A) (k : K) :
  k ∈ keys m ↔ is_Some (m !! k).
Proof.
unfold keys; split; intros Hk.
simpl_elem_of; intuition. destruct Hk as [x Hx].
apply elem_of_list_fmap; exists (k, x); split; [done|].
apply elem_of_map_to_list; done.
Qed.

Lemma elem_of_values `{FinMap K M} {A} (m : M A) (x : A) :
  x ∈ values m ↔ ∃ k, m !! k = Some x.
Proof.
unfold values; split; intros Hx.
simpl_elem_of; exists k; done. destruct Hx as [k Hk].
apply elem_of_list_fmap; exists (k, x); split; [done|].
apply elem_of_map_to_list; done.
Qed.

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
intros; apply NoDup_Permutation.
1,2: apply NoDup_list_union; done.
intros; rewrite ?elem_of_list_union; tauto.
Qed.

Lemma Permutation_app_split `{EqDecision A} (P : A -> Prop) l1 l2 l3 l4 :
  Forall (not ∘ P) l1 -> Forall P l2 ->
  Forall (not ∘ P) l3 -> Forall P l4 ->
  l1 ++ l2 ≡ₚ l3 ++ l4 -> l1 ≡ₚ l3 ∧ l2 ≡ₚ l4.
Proof.
intros H1 H2 H3 H4 Hp;
apply Permutation_cross_split in Hp as (lac&lad&lbc&lbd&H1'&H2'&H3'&H4').
destruct lad; [destruct lbc|]; cbn in *; rewrite ?app_nil_r in H1', H3'.
- rewrite <-H1', <-H2', <-H3', <-H4'; done.
- rewrite Permutation_app_comm in H3'; cbn in H3'; symmetry in H2', H3'.
  assert (Ha1 : a ∈ l2) by (apply elem_of_Permutation; eexists; done).
  assert (Ha2 : a ∈ l3) by (apply elem_of_Permutation; eexists; done).
  eapply Forall_forall in Ha1, Ha2; [|apply H3|apply H2]; done.
- rewrite Permutation_app_comm in H1'; cbn in H1'; symmetry in H1', H4'.
  assert (Ha1 : a ∈ l1) by (apply elem_of_Permutation; eexists; done).
  assert (Ha2 : a ∈ l4) by (apply elem_of_Permutation; eexists; done).
  eapply Forall_forall in Ha1, Ha2; [|apply H4|apply H1]; done.
Qed.

Section Pmap_keys.

Global Instance :
  PreOrder Psuffix.
Proof.
split.
- intros x; induction x; cbn; done.
- intros x; induction x; destruct y, z; firstorder.
Qed.

Lemma Psuffix_app s i j :
  Psuffix s i -> Psuffix s (j ++ i).
Proof.
revert s; induction i; destruct s; cbn; firstorder.
Qed.

Lemma Psuffix_app_inv s i j :
  Pos.size s ≤ Pos.size i -> Psuffix s (j ++ i) -> Psuffix s i.
Proof.
revert s; induction i; destruct s; cbn; firstorder.
1,2: apply IHi; try done. all: lia.
Qed.

Lemma gt_not_Psuffix i j :
  i > j -> ¬ Psuffix i j.
Proof.
revert j; induction i; destruct j;
cbn; intros; firstorder; lia.
Qed.

Lemma gt_Papp i1 i2 j :
  i1 > i2 -> i1 ++ j > i2 ++ j.
Proof.
induction j; cbn; lia.
Qed.

Lemma size_Preverse_go i j :
  Pos.size (Preverse_go i j) = Pos.size i + Pos.size j - 1.
Proof.
revert i; induction j; cbn; intros.
1,2: rewrite IHj; cbn; lia. lia.
Qed.

Lemma size_Preverse i :
  Pos.size (Preverse i) = Pos.size i.
Proof.
unfold Preverse; rewrite size_Preverse_go, Pos.add_comm; cbn; lia.
Qed.

Variable A : Type.
Implicit Types m : Pmap_raw A.

Lemma Psuffix_pmap_keys i j m :
  Psuffix (Preverse i) (Preverse j) ->
  Forall (Psuffix (Preverse i)) (pmap_keys j m).
Proof.
revert j; induction m; cbn; intros. done.
repeat (apply Forall_app; split).
- destruct o; [apply Forall_singleton|done]; done.
- apply IHm1; rewrite Preverse_xO; apply Psuffix_app; done.
- apply IHm2; rewrite Preverse_xI; apply Psuffix_app; done.
Qed.

Lemma not_Psuffix_pmap_keys i j m :
  Pos.size i ≤ Pos.size j ->
  ¬ Psuffix (Preverse i) (Preverse j) ->
  Forall (not ∘ Psuffix (Preverse i)) (pmap_keys j m).
Proof.
revert j; induction m; cbn; intros j H1 H2. done.
repeat (apply Forall_app; split).
- destruct o; [apply Forall_singleton|done]; done.
- apply IHm1; [cbn; lia|]; rewrite Preverse_xO; intros H3; apply H2.
  eapply Psuffix_app_inv; [|apply H3]. rewrite ?size_Preverse; done.
- apply IHm2; [cbn; lia|]; rewrite Preverse_xI; intros H3; apply H2.
  eapply Psuffix_app_inv; [|apply H3]. rewrite ?size_Preverse; done.
Qed.

Lemma pmap_keys_Permutation_raw j m1 m2 :
  pmap_keys j m1 ≡ₚ pmap_keys j m2 ->
  pmap_keys j m1 = pmap_keys j m2.
Proof.
revert j m2; induction m1; cbn; intros. simpl_Permutation; done.
destruct m2; cbn in *. simpl_Permutation; done. rewrite ?app_assoc in H.
apply Permutation_app_split with (P:=Psuffix (Preverse j~1)) in H as [H H1].
apply Permutation_app_split with (P:=Psuffix (Preverse j~0)) in H as [H H0].
rewrite (IHm1_1 _ m2_1), (IHm1_2 _ m2_2); try done.
destruct o, o0; try done; simpl_Permutation; done.
all: try (apply Forall_app; split).
all: try (apply Psuffix_pmap_keys; done).
all: try (apply not_Psuffix_pmap_keys; [cbn; lia|]).
4,6: rewrite Preverse_xO, Preverse_xI; apply gt_not_Psuffix, gt_Papp; lia.
1,3: destruct o; try done. 3,4: destruct o0; try done.
all: apply Forall_singleton, gt_not_Psuffix.
all: rewrite ?Preverse_xO, ?Preverse_xI.
all: rewrite <-(Papp_1_l (Preverse _)) at 2.
all: apply gt_Papp; lia.
Qed.

Lemma pmap_keys_spec_raw j m acc :
  (Pto_list_raw j m acc).*1 = pmap_keys j m ++ acc.*1.
Proof.
revert j acc; induction m; cbn; intros. done.
rewrite fmap_app, IHm1, IHm2, <-?app_assoc; destruct o; done.
Qed.

Lemma pmap_keys_spec (m : Pmap A) :
  keys m = pmap_keys 1 (pmap_car m).
Proof.
unfold keys, map_to_list, Pto_list; destruct m as [car prf]; cbn.
rewrite pmap_keys_spec_raw, app_nil_r; done.
Qed.

Corollary pmap_keys_Permutation (m1 m2 : Pmap A) :
  keys m1 ≡ₚ keys m2 -> keys m1 = keys m2.
Proof.
rewrite ?pmap_keys_spec; apply pmap_keys_Permutation_raw.
Qed.

End Pmap_keys.
