(* Permutations based on Pmap from std++. *)

Require Import DecimalString.
From stdpp Require Import strings.
From stdpp Require Export base numbers option list pmap.

Global Open Scope positive_scope.
Global Open Scope list_scope.

Definition prod_swap {X} (p : X * X) :=
  match p with (x1, x2) => (x2, x1) end.

Definition pmap_swap (i j : positive) : Pmap positive :=
  {[i:=j; j:=i]}.

Definition pmap_apply (m : Pmap positive) (i : positive) : positive :=
  default i (m !! i).

Definition pmap_compose (m1 m2 : Pmap positive) : Pmap positive :=
  merge (from_option Some) m2 (pmap_apply m2 <$> m1).

Definition pmap_invert (m : Pmap positive) : Pmap positive :=
  list_to_map (prod_swap <$> map_to_list m).

Definition FinInj `{Lookup X X (M X)} (m : M X) :=
  ∀ x1 x2 y, m !! x1 = Some y -> m !! x2 = Some y -> x1 = x2.

Definition FinSurj `{Lookup X X (M X)} (m : M X) :=
  ∀ y z, m !! y = Some z -> ∃ x, m !! x = Some y.

Definition FinCoSurj `{Lookup X X (M X)} (m : M X) :=
  ∀ x y, m !! x = Some y -> ∃ z, m !! y = Some z.

Local Ltac simpl_inj :=
  repeat match goal with
  | inj : FinInj ?m, H1 : ?m !! ?i = Some ?y, H2 : ?m !! ?j = Some ?y |- _ =>
    let H := fresh in assert (H := inj _ _ _ H1 H2); clear H1; subst
  end.

Local Ltac simpl_elem_of :=
  repeat match goal with
  | H : ?x ∈ ?f <$> ?l |- _ =>
    apply elem_of_list_fmap in H as ([] & ? & H)
  | H : _ ∈ map_to_list _ |- _ =>
    apply elem_of_map_to_list in H
  end.

Local Ltac simpl_lookup :=
  repeat match goal with
  | H : {[_:=_]} !! _ = Some _ |- _ =>
    apply lookup_singleton_Some in H as []
  | H : <[_:=_]> _ !! _ = Some _ |- _ =>
    apply lookup_insert_Some in H as [[]|[]]; subst
  | H : delete _ _ !! _ = Some _ |- _ =>
    apply lookup_delete_Some in H as []
  end.

Section Bijection.

Section Pmap_Bijection.

Lemma finj_if_inj m :
  Inj eq eq (pmap_apply m) -> FinInj m.
Proof.
unfold pmap_apply; intros inj x1 x2 y H1 H2.
apply inj; rewrite H1, H2; done.
Qed.

Lemma fsurj_iff_surj m :
  Surj eq (pmap_apply m) ↔ FinSurj m.
Proof.
unfold pmap_apply; split; intros surj y.
- intros z Hz; destruct (surj y) as [x Hy], (m !! x) eqn:Hx; cbn in Hy; subst.
  eexists; done. congruence.
- destruct (m !! y) eqn:H. apply surj in H as [x]; exists x; rewrite H; done.
  exists y; rewrite H; done.
Qed.

Local Ltac decide_neq P :=
  destruct (decide P); [subst; congruence|].

Lemma fcosurj_if_finj_fsurj (m : Pmap positive) :
  FinInj m -> FinSurj m -> FinCoSurj m.
Proof.
remember (size m) as n; revert Heqn; revert m.
induction n; intros m Hn inj surj; symmetry in Hn.
- apply map_size_empty_inv in Hn; subst; done.
- intros x y Hx; apply surj in Hx as Hu; destruct Hu as [u Hu].
  destruct (m !! y) as [z|] eqn:Hy. eexists; done. exfalso.
  decide_neq (x = y); decide_neq (x = y);
  decide_neq (u = x); decide_neq (u = y).
  cut (FinCoSurj (<[u:=y]> (delete x m))); [intros co_surj|apply IHn].
  + destruct (co_surj u y); simplify_map_eq; done.
  + rewrite map_size_insert, map_size_delete, Hn; simpl_map; done.
  + intros x1 x2 y' H1 H2; simpl_lookup; simpl_inj; eapply inj; done.
  + intros y' z' H'; simpl_lookup.
    * apply surj in Hu as Hx'; destruct Hx' as [x' Hx'].
      decide_neq (x' = y'); decide_neq (x' = x). exists x'; simpl_map; done.
    * apply surj in H1 as Hx'; destruct Hx' as [x' Hx'].
      decide_neq (x' = u); decide_neq (x' = x). exists x'; simpl_map; done.
Qed.

Lemma inj_if_finj_fsurj m :
  FinInj m -> FinSurj m -> Inj eq eq (pmap_apply m).
Proof.
unfold pmap_apply; intros inj surj x1 x2.
assert (co_surj : FinCoSurj m) by now apply fcosurj_if_finj_fsurj.
destruct (m !! x1) eqn:H1, (m !! x2) eqn:H2; cbn; intros; subst.
eapply inj; done. apply co_surj in H1 as []; congruence.
apply co_surj in H2 as []; congruence. done.
Qed.

End Pmap_Bijection.

Lemma pmap_empty_inj :
  FinInj (∅ : Pmap positive).
Proof.
done.
Qed.

Lemma pmap_empty_surj :
  FinSurj (∅ : Pmap positive).
Proof.
intros x; done.
Qed.

Lemma pmap_swap_inj i j :
  FinInj (pmap_swap i j).
Proof.
intros x1 x2; unfold pmap_swap; intros; simpl_lookup; subst; done.
Qed.

Lemma pmap_swap_surj i j :
  FinSurj (pmap_swap i j).
Proof.
intros y z; unfold pmap_swap; intros; exists z.
destruct (decide (i = j)); simpl_lookup; subst; simplify_map_eq; done.
Qed.

Section Compose.

Lemma contra {P Q : Prop} :
  (P -> Q) -> ¬ Q -> ¬ P.
Proof.
auto.
Qed.

Lemma apply_pmap_compose_inj m1 m2 :
  Inj eq eq (pmap_apply m1) ->
  Inj eq eq (pmap_apply m2) ->
  Inj eq eq (pmap_apply (pmap_compose m1 m2)).
Proof.
repeat unfold pmap_apply, pmap_compose; intros H1 H2 x1 x2.
rewrite ?lookup_merge, ?lookup_fmap; intros H3.
destruct (decide (x1 = x2)) as [H4|H4]; [done|exfalso].
assert (H5 := contra (H1 _ _) H4); cbn in *;
repeat destruct (m1 !! _); cbn in *;
assert (H6 := contra (H2 _ _) H5); cbn in *;
repeat destruct (m2 !! _); done.
Qed.

Lemma apply_pmap_compose_surj m1 m2 :
  Surj eq (pmap_apply m1) ->
  Surj eq (pmap_apply m2) ->
  Surj eq (pmap_apply (pmap_compose m1 m2)).
Proof.
repeat unfold pmap_apply, pmap_compose; intros H1 H2 z.
destruct (H2 z) as [y Hy], (H1 y) as [x Hx]; exists x.
rewrite lookup_merge, lookup_fmap; simplify_option_eq.
destruct (m1 !! x) as [y|]; cbn.
destruct (m2 !! x), (m2 !! y); done.
destruct (m2 !! x); done.
Qed.

Lemma pmap_compose_inj (m1 m2 : Pmap positive) :
  FinInj m1 -> FinSurj m1 ->
  FinInj m2 -> FinSurj m2 ->
  FinInj (pmap_compose m1 m2).
Proof.
intros; apply finj_if_inj, apply_pmap_compose_inj;
apply inj_if_finj_fsurj; done.
Qed.

Lemma pmap_compose_surj m1 m2 :
  FinSurj m1 -> FinSurj m2 -> FinSurj (pmap_compose m1 m2).
Proof.
intros; apply fsurj_iff_surj, apply_pmap_compose_surj;
apply fsurj_iff_surj; done.
Qed.

End Compose.

Section Invert.

Global Instance prod_swap_inj {X} :
  Inj eq eq (@prod_swap X).
Proof.
intros [] []; cbn; congruence.
Qed.

Lemma NoDup_fst_prod_swap_map_to_list (m : Pmap positive) :
  FinInj m -> NoDup (prod_swap <$> map_to_list m).*1.
Proof.
intros inj; apply NoDup_fmap_fst; intros.
simpl_elem_of; simplify_eq/=; simpl_inj; done.
apply NoDup_fmap. apply prod_swap_inj. apply NoDup_map_to_list.
Qed.

Lemma pmap_invert_None m x :
  FinInj m -> FinSurj m -> m !! x = None -> pmap_invert m !! x = None.
Proof.
(* This is NOT a direct consequence of the other lemmas, since pmap_invert would
still be allowed to contain redundant identity mappings that are not in m.
According to this lemma it does not contain such redundant mappings. *)
unfold pmap_invert; intros inj surj Hx; apply not_elem_of_list_to_map; intros H.
assert (co_surj : FinCoSurj m) by now apply fcosurj_if_finj_fsurj.
simpl_elem_of; simplify_eq/=; apply co_surj in H as []; congruence.
Qed.

Lemma pmap_invert_None_inv m x :
  FinSurj m -> pmap_invert m !! x = None -> m !! x = None.
Proof.
unfold pmap_invert; intros surj Hx.
destruct (m !! x) as [y|] eqn:H; [exfalso|done]; apply surj in H as [z].
apply not_elem_of_list_to_map in Hx; apply Hx; clear Hx.
apply elem_of_list_fmap; exists (x, z); repeat split. 
apply elem_of_list_fmap; exists (z, x); repeat split.
apply elem_of_map_to_list; done.
Qed.

Lemma pmap_invert_Some m x y :
  FinInj m -> m !! x = Some y -> pmap_invert m !! y = Some x.
Proof.
unfold pmap_invert; intros inj Hx; apply elem_of_list_to_map.
apply NoDup_fst_prod_swap_map_to_list; done.
apply elem_of_list_fmap; exists (x, y); repeat split.
apply elem_of_map_to_list; done.
Qed.

Lemma pmap_invert_Some_inv m x y :
  FinInj m -> pmap_invert m !! y = Some x -> m !! x = Some y.
Proof.
unfold pmap_invert; intros inj Hy; apply elem_of_list_to_map in Hy.
simpl_elem_of; simplify_eq/=; done.
apply NoDup_fst_prod_swap_map_to_list; done.
Qed.

Lemma pmap_invert_inj m :
  FinInj m -> FinInj (pmap_invert m).
Proof.
intros inj x1 x2 y H1 H2.
apply pmap_invert_Some_inv in H1, H2; [congruence|done|done].
Qed.

Lemma pmap_invert_surj m :
  FinInj m -> FinSurj m -> FinSurj (pmap_invert m).
Proof.
intros inj surj y z Hy; apply pmap_invert_Some_inv in Hy; [|done].
assert (co_surj : FinCoSurj m) by now apply fcosurj_if_finj_fsurj.
apply co_surj in Hy as [x Hx]; exists x.
apply pmap_invert_Some; done.
Qed.

End Invert.

End Bijection.

Inductive perm := Perm {
  perm_car  : Pmap positive;
  perm_inj  : FinInj perm_car;
  perm_surj : FinSurj perm_car;
}.

Global Instance : FinMapToList positive positive perm :=
  λ π, map_to_list (perm_car π).

Global Instance perm_lookup : LookupTotal positive positive perm :=
  λ i π, pmap_apply (perm_car π) i.

Global Instance : Empty perm :=
  Perm _ pmap_empty_inj pmap_empty_surj.

Definition perm_swap (i j : positive) :=
  Perm _ (pmap_swap_inj i j) (pmap_swap_surj i j).

Definition perm_compose (τ π : perm) :=
  let (τ_m, τ_inj, τ_surj) := τ in
  let (π_m, π_inj, π_surj) := π in Perm _
    (pmap_compose_inj _ _ τ_inj τ_surj π_inj π_surj)
    (pmap_compose_surj _ _ τ_surj π_surj).

Definition perm_invert (π : perm) :=
  let (π_m, π_inj, π_surj) := π in Perm _
    (pmap_invert_inj _ π_inj)
    (pmap_invert_surj _ π_inj π_surj).

Notation "⟨ i ; j ⟩" := (perm_swap i j) (format "⟨ i ;  j ⟩").
Notation "π ⋅ τ" := (perm_compose τ π) (at level 15).
Notation "(⋅)" := perm_compose (only parsing).
Notation inv := perm_invert.

Definition perm_cycle (i : positive) (is : list positive) : perm :=
  foldl (λ π j, ⟨i; j⟩ ⋅ π) ∅ is.

Notation "⟨ i ; x ; y ; .. ; z ⟩" :=
  (perm_cycle i (cons x (cons y .. (cons z nil) ..)))
  (format "⟨ i ;  x ;  y ;  .. ;  z ⟩").

Section Group.

Class Group (X : Type) `{_equiv : Equiv X}
  (f : X -> X -> X) (inv : X -> X) (e : X) : Prop :=
{
  Group_Equivalence :> Equivalence (≡);
  Group_Proper      :> Proper ((≡) ==> (≡) ==> (≡)) f;
  Group_Assoc       :> Assoc (≡) f;
  Group_LeftId      :> LeftId (≡) e f;
  Group_RightId     :> RightId (≡) e f;
  left_inv x        : f (inv x) x ≡ e;
  right_inv x       : f x (inv x) ≡ e;
}.

Lemma lookup_compose π τ i :
  π ⋅ τ !!! i = π !!! (τ !!! i).
Proof.
destruct τ as [τ_m ? ?], π as [π_m ? ?]; unfold lookup_total, perm_lookup; cbn.
unfold pmap_apply, pmap_compose; rewrite lookup_merge, lookup_fmap.
destruct (τ_m !! i) as [i1|]; cbn; unfold pmap_apply.
destruct (π_m !! i) as [i0|], (π_m !! i1); done.
destruct (π_m !! i) as [i0|]; done.
Qed.

Global Instance : Equiv perm :=
  λ τ π, ∀ i, τ !!! i = π !!! i.

Global Instance :
  Group _ (⋅) inv ∅.
Proof.
split; repeat intros ?; rewrite ?lookup_compose; cbn; try done.
split; congruence. etrans; auto; f_equal; done.
all: unfold lookup_total, perm_lookup, pmap_apply.
all: destruct x as [m inj surj]; cbn.
- destruct (_ !! i) eqn:H; cbn.
  apply pmap_invert_Some_inv in H as ->; done.
  apply pmap_invert_None_inv in H as ->; done.
- destruct (_ !! i) eqn:H; cbn.
  apply pmap_invert_Some in H as ->; done.
  apply pmap_invert_None in H as ->; done.
Qed.

End Group.

Section Print.

Definition cycle := list positive.

(* Append a cycle segment to a list of cycles. *)
Fixpoint cycles_add (cycles : list (positive * cycle * positive))
  (i0 : positive) (is : cycle) (ik : positive) :=
  match cycles with
  | [] => [(i0, is, ik)]
  | (j0, js, jk) :: cs =>
    if decide (ik = j0)
    then cycles_add cs i0 (is ++ [ik] ++ js) jk
    else if decide (i0 = jk)
    then cycles_add cs j0 (js ++ [i0] ++ is) ik
    else (j0, js, jk) :: cycles_add cs i0 is ik
  end.

(* Convert a permutation to a list of cycles. *)
Definition perm_cycles (π : perm) : list cycle :=
  (λ c, match c with (i0, is, ik) => i0 :: is ++ [ik] end) <$>
  (foldl (λ cs m, match m with (i, j) =>
    if decide (i = j) then cs
    else cycles_add cs i [] j end)
    [] (map_to_list π)).

Fixpoint str_join (sep : string) (l : list string) :=
  match l with
  | [] => ""
  | [x] => x
  | x :: l' => x +:+ sep +:+ str_join sep l'
  end.

Definition str_of_pos i :=
  NilZero.string_of_uint (Pos.to_uint i).

Definition str_of_cycle (c : cycle) :=
  "(" +:+ str_join " " (map str_of_pos (removelast c)) +:+ ")".

Definition str_of_perm (π : perm) :=
  str_join "" (str_of_cycle <$> perm_cycles π).

End Print.
