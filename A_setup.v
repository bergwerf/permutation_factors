(* General purpose notations. *)

Require Vector.
Require Import Utf8 Bool List PeanoNat PArith BinNums.
Export Utf8 List ListNotations PeanoNat PArith BinNums.

(******************************************************************************)
(* I. Global notations.                                                       *)
(******************************************************************************)

(* Sigma types. *)
Notation "'Σ' x .. y , P" := (sigT (λ x, .. (sigT (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' Σ  x .. y ']' ,  '/' P ']'") : type_scope.

(* Functions on nat without importing the proofs *)
Notation min := (Nat.min).
Notation max := (Nat.max).

(* Cartesian products. *)
Notation "A × B" := (prod A B) (at level 100).

(* Boolean vectors. *)
Notation vec := (Vector.t bool).

(******************************************************************************)
(* II. Global tactics.                                                        *)
(******************************************************************************)

Ltac inv H := inversion H; subst; clear H; try easy.

Ltac convert_bool_once :=
  match goal with
  | [H : _ && _ = true |- _] =>  apply andb_prop in H; destruct H
  | [H : _ || _ = true |- _]  => apply orb_true_elim in H; destruct H
  | [H : _ || _ = false |- _]  => apply orb_false_elim in H; destruct H
  | [H : _ =? _ = true |- _]   => apply Nat.eqb_eq in H
  | [H : _ =? _ = false |- _]  => apply Nat.eqb_neq in H
  | [H : _ <=? _ = true |- _]  => apply Nat.leb_le in H
  | [H : _ <=? _ = false |- _] => apply Nat.leb_gt in H
  | [H : _ <? _ = true |- _]   => apply Nat.ltb_lt in H
  | [H : _ <? _ = false |- _]  => apply Nat.ltb_ge in H
  | |- (_ && _ = true)   => apply andb_true_intro; split
  | |- (_ || _ = false)  => apply orb_false_intro
  | |- (_ || _ = true)   => apply orb_true_intro
  | |- (_ =? _ = true)   => apply Nat.eqb_eq
  | |- (_ =? _ = false)  => apply Nat.eqb_neq
  | |- (_ <=? _ = true)  => apply Nat.leb_le
  | |- (_ <=? _ = false) => apply Nat.leb_gt
  | |- (_ <? _ = true)   => apply Nat.ltb_lt
  | |- (_ <? _ = false)  => apply Nat.ltb_ge
  | _ => idtac
  end.

Ltac convert_bool := repeat convert_bool_once.

Lemma wd {X Y} (f : X -> Y) x x' :
  x = x' -> f x = f x'.
Proof.
congruence.
Qed.
