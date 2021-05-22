(* General purpose notations. *)

Require Import Utf8 Bool List PeanoNat PArith BinNums.
Export Utf8 Bool List ListNotations PeanoNat PArith BinNums.

Open Scope positive.

(******************************************************************************)
(* I. Global notations.                                                       *)
(******************************************************************************)

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* List inclusion. *)
Notation "l ⊆ m" := (incl l m) (at level 70).

(* Option unpacking. *)
Notation "opt ?? d" :=
  (match opt with Some v => v | None => d end)
  (at level 50).

(******************************************************************************)
(* II. Global tactics.                                                        *)
(******************************************************************************)

Ltac inv H := inversion H; subst; clear H; try easy.
Ltac simple_ind x := induction x; simpl; intros; [easy|].

Ltac convert_bool_once :=
  match goal with
  | [H : _ && _ = true |- _] =>  apply andb_prop in H; destruct H
  | [H : _ || _ = true |- _]  => apply orb_true_elim in H; destruct H
  | [H : _ || _ = false |- _]  => apply orb_false_elim in H; destruct H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ || _ = false)  => apply orb_false_intro
  | |- (_ || _ = true)   => apply orb_true_intro
  | _ => idtac
  end.

Ltac convert_Nat_bool_once :=
  match goal with
  | [H : _ =? _ = true |- _]   => apply Nat.eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply Nat.eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply Nat.leb_le in H
  | [H : _ <=? _ = false |- _] => apply Nat.leb_gt in H
  | [H : _ <? _ = true |- _]   => apply Nat.ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply Nat.ltb_ge in H
  | |- (_ =? _ = true)   => apply Nat.eqb_eq
  | |- (_ =? _ = false)  => apply Nat.eqb_neq
  | |- (_ <=? _ = true)  => apply Nat.leb_le
  | |- (_ <=? _ = false) => apply Nat.leb_gt
  | |- (_ <? _ = true)   => apply Nat.ltb_lt
  | |- (_ <? _ = false)  => apply Nat.ltb_ge
  | _ => idtac
  end.

Ltac convert_Pos_bool_once :=
  match goal with
  | [H : _ =? _ = true |- _]   => apply Pos.eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply Pos.eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply Pos.leb_le in H
  | [H : _ <=? _ = false |- _] => apply Pos.leb_gt in H
  | [H : _ <? _ = true |- _]   => apply Pos.ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply Pos.ltb_ge in H
  | |- (_ =? _ = true)   => apply Pos.eqb_eq
  | |- (_ =? _ = false)  => apply Pos.eqb_neq
  | |- (_ <=? _ = true)  => apply Pos.leb_le
  | |- (_ <=? _ = false) => apply Pos.leb_gt
  | |- (_ <? _ = true)   => apply Pos.ltb_lt
  | |- (_ <? _ = false)  => apply Pos.ltb_ge
  | _ => idtac
  end.

Ltac convert_bool :=
  repeat convert_bool_once;
  repeat convert_Nat_bool_once;
  repeat convert_Pos_bool_once.

Lemma wd {X Y} (f : X -> Y) x x' :
  x = x' -> f x = f x'.
Proof.
congruence.
Qed.
