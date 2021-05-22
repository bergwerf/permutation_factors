(* Additional theorems about list operations. *)

From CGT Require Import A1_setup.
Require Import Wf_nat.

Local Close Scope positive.

Section Lists.

Variable X : Type.
Hypothesis eq_dec : ∀x x' : X, {x = x'} + {x ≠ x'}.

Theorem nodup_dec (l : list X) :
  {NoDup l} + {∃l0 x l1, l = l0 ++ x :: l1 /\ In x l1}.
Proof.
induction l. left; apply NoDup_nil.
destruct IHl. destruct (in_dec eq_dec a l).
- right; exists [], a, l; easy.
- left; apply NoDup_cons; easy.
- right; destruct e as [l0 [x [l1 []]]]; subst.
  exists (a :: l0), x, l1; easy.
Qed.

Theorem app_cut (l0 l0' l1 l1' : list X) :
  l0 ++ l0' = l1 ++ l1' -> length l0 = length l1 -> l0 = l1 /\ l0' = l1'.
Proof.
revert l0' l1 l1'; induction l0; intros; destruct l1; try easy.
inv H. apply IHl0 in H3 as []; subst. easy.
simpl in H0; inv H0.
Qed.

Theorem map_singleton_eq {Y} (f : X -> Y) x y :
  map f [x] = [y] -> f x = y.
Proof.
simpl; intros H; inv H.
Qed.

Theorem fold_left_skipn {Y} (f : Y -> X -> Y) l n y :
  fold_left f l y = fold_left f (skipn n l) (fold_left f (firstn n l) y).
Proof.
revert l y; induction n; destruct l; simpl; easy.
Qed.

Theorem firstn_incl n (l : list X) :
  firstn n l ⊆ l.
Proof.
revert l; induction n; destruct l; simpl.
1-3: apply incl_nil_l. apply incl_cons.
apply in_eq. apply incl_tl, IHn.
Qed.

Theorem skipn_incl n (l : list X) :
  skipn n l ⊆ l.
Proof.
revert l; induction n; destruct l; simpl.
1,3: apply incl_nil_l. apply incl_refl.
apply incl_tl, IHn.
Qed.

Section Well_founded_induction.

Variable P : list X -> Prop.
Hypothesis IH : ∀l, (∀l', length l' < length l -> P l') -> P l.

Theorem lt_length_wf_ind l :
  P l.
Proof.
remember (length l) as n; revert Heqn; revert l.
apply (lt_wf_ind n); clear n; intros n IH' l H; subst.
apply IH; intros. apply IH' with (m:=length l'); easy.
Qed.

End Well_founded_induction.

End Lists.
