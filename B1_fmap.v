(* Storing finite maps as unbalanced binary trees. *)

From permutation_solver Require Import A_setup.

Open Scope positive.

(***
We start with some utilities for positive numbers.
*)

(***
Using an unbalanced tree has several interesting advantages:
- Implementation is simpler.
- Creation does not require balancing.
- Lookup does not require key comparison.
*)

Inductive fmap := Ident | Node (i : positive) (f0 f1 : fmap).

(* Get the submap under a given branch. *)
Fixpoint truncate (f : fmap) (i : positive) :=
  match f with
  | Ident => Ident
  | Node j f0 f1 =>
    match i with
    | xH => f
    | xO i' => truncate f0 i'
    | xI i' => truncate f1 i'
    end
  end.

(* Apply f to i. The input index must be repeated for the Ident case. *)
Fixpoint apply (f : fmap) (i : positive) : positive -> positive :=
  match f with
  | Ident => λ j, j
  | Node j f0 f1 =>
    match i with
    | xH => λ _, j
    | xO i' => apply f0 i'
    | xI i' => apply f1 i'
    end
  end.

Notation "f ⋅ i" := (apply f i i) (at level 5, format "f ⋅ i").

(* Apply g after f. The initial input for g must be copied as gI. *)
Fixpoint compose (gI g f : fmap) {struct f} :=
  match f with
  | Ident => g
  | Node j f0 f1 =>
    match g with
    | Ident => Node (gI⋅j) (compose gI Ident f0) (compose gI Ident f1)
    | Node _ g0 g1 => Node (gI⋅j) (compose gI g0 f0) (compose gI g1 f1)
    end
  end.

(* Reverse a positive number (path to index) andd add to accumulator. *)
Fixpoint revp (r acc : positive) :=
  match r with
  | xH => acc
  | xO r' => revp r' (xO acc)
  | xI r' => revp r' (xI acc)
  end.

(* Prune identity branches give we are at branch r. *)
Fixpoint prune (f : fmap) (r : positive) :=
  match f with
  | Ident => Ident
  | Node j f0 f1 =>
    match prune f0 (xO r), prune f1 (xI r) with
    | Ident, Ident => if revp r xH =? j then Ident else Node j Ident Ident
    | f0', f1' => Node j f0' f1'
    end
  end.

Notation "g ∘ f" := (prune (compose g g f) xH) (at level 50).

(***
Lets state some boring, obvious results.
*)

Lemma fmap_eq_dec (f g : fmap) :
  {f = g} + {f ≠ g}.
Proof.
revert g; induction f as [|j f0 Hf0 f1 Hf1]; intros [].
now left. 1,2: now right.
destruct (Pos.eq_dec j i); subst.
destruct (Hf0 f2); subst.
destruct (Hf1 f3); subst.
now left. all: right; congruence.
Qed.

(***
We now want to prove that composition and pruning agree with application.
*)

Lemma revp_shift_xO r i : revp r i~0 = revp r~0 i.
Proof. easy. Qed.

Lemma revp_shift_xI r i : revp r i~1 = revp r~1 i.
Proof. easy. Qed.

(* Pruning does not alter the mapping. *)
Theorem prune_apply f r i :
  apply (prune f r) i (revp r i) = apply f i (revp r i).
Proof.
revert r i; induction f as [|j f0 IHf0 f1 IHf1]; intros. easy.
simpl prune. destruct (prune f0 _) eqn:H0. destruct (prune f1 _) eqn:H1.
(* The second and third goal are actually exactly the same. *)
2: rewrite <-H0, <-H1; clear H0 H1. 3: rewrite <-H0; clear H0.
(* First solve the double Ident case. *)
{ destruct (revp r 1 =? j) eqn:E; simpl; destruct i.
  2,5: rewrite revp_shift_xO, <-IHf0, H0; easy.
  1,3: rewrite revp_shift_xI, <-IHf1, H1; easy.
  apply Pos.eqb_eq, E. reflexivity. }
(* Solve the remaining goals simultaneously.*)
all: simpl; destruct i; try reflexivity.
2,4: rewrite revp_shift_xO, <-IHf0; easy.
1,2: rewrite revp_shift_xI, <-IHf1; easy.
Qed.

Corollary prune_xH_apply f i :
  (prune f xH)⋅i = f⋅i.
Proof.
apply prune_apply.
Qed.

(* If f is Ident at i, then f⋅i = i. *)
Lemma truncate_Ident_apply f i iI :
  truncate f i = Ident -> apply f i iI = iI.
Proof.
revert i; induction f as [|j f0 IHf0 f1 IHf1]; simpl; intros. easy.
destruct i. apply IHf1, H. apply IHf0, H. discriminate H.
Qed.

(* If f is the identity at i, then the sub-branch of g is used. *)
Lemma compose_apply_Ident gI g f i iI :
  truncate f i = Ident -> apply (compose gI g f) i iI = apply g i iI.
Proof.
revert g i iI; induction f as [|j f0 IHf0 f1 IHf1]; simpl; intros. easy.
destruct i, g; simpl; try discriminate H.
rewrite IHf1; easy. apply IHf1, H.
rewrite IHf0; easy. apply IHf0, H.
Qed.

(* If f is not the identity at i, then gI is applied to the node value. *)
Lemma compose_apply_not_Ident gI g f i iI :
  truncate f i ≠ Ident -> apply (compose gI g f) i iI = gI⋅(apply f i iI).
Proof.
revert g i iI; induction f as [|j f0 IHf0 f1 IHf1]; intros. easy.
destruct g, i; simpl in *; try reflexivity.
2,4: apply IHf0, H. 1,2: apply IHf1, H.
Qed.

Theorem compose_apply g f i :
  (compose g g f)⋅i = g⋅(f⋅i).
Proof.
(* We split into two cases based on `truncate f i`. *)
destruct (truncate f i) eqn:H.
- eapply truncate_Ident_apply in H as Hf; rewrite Hf.
  apply compose_apply_Ident, H.
- apply compose_apply_not_Ident; congruence.
Qed.

Corollary comp_apply g f i :
  (g ∘ f)⋅i = g⋅(f⋅i).
Proof.
etransitivity.
apply prune_apply.
apply compose_apply.
Qed.
