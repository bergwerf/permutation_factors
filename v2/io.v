(* Input and output of permutations. *)

Require Import PArith DecimalString.
From stdpp Require Import base list strings pmap.

Global Open Scope positive_scope.
Global Open Scope list_scope.

Definition perm := Pmap positive.

Module Cycles.

(* Define cycles as a linear lookup list. *)

Definition cycle := list positive.

Fixpoint linear_lookup (c : cycle) (i : positive) :=
  match c with
  | [] => i
  | [_] => i
  | i' :: (j :: _) as c' =>
    if decide (i = i') then j
    else linear_lookup c' i
  end.

(* Convert pmap to cycles. *)

Fixpoint linear_insert (cs : list (positive * cycle * positive))
  (d0 : positive) (d : cycle) (dn : positive) :=
  match cs with
  | [] => [(d0, d, dn)]
  | (c0, c, cn) :: cs' =>
    if decide (dn = c0)
    then linear_insert cs' d0 (d ++ [dn] ++ c) cn
    else if decide (d0 = cn)
    then linear_insert cs' c0 (c ++ [d0] ++ d) dn
    else (c0, c, cn) :: linear_insert cs' d0 d dn
  end.

Definition unpack (π : perm) : list cycle := map
  (λ ct, match ct with (c0, c, cn) => c0 :: c ++ [cn] end)
  (fold_left (λ cs m, match m with (i, j) =>
      if decide (i = j) then cs
      else linear_insert cs i [] j end)
    (Pto_list π) []).

(* Convert cycles to pmap. *)

Fixpoint pack_cycle (π : perm) (c : cycle) :=
  match c with
  | [] => π
  | [_] => π
  | i :: (j :: _) as c' => <[i:=j]>(pack_cycle π c')
  end.

Definition pack (cs : list cycle) : perm :=
  fold_left pack_cycle cs ∅.

(* Print a permutation using cycle notation. *)

Fixpoint str_join sep l :=
  match l with
  | [] => ""
  | [x] => x
  | x :: l' => x +:+ sep +:+ str_join sep l'
  end.

Definition str_of_pos i :=
  NilZero.string_of_uint (Pos.to_uint i).

Definition str_of_cycle (c : cycle) :=
  "(" +:+ str_join " " (map str_of_pos (removelast c)) +:+ ")".

Definition print (π : perm) :=
  str_join " " (map str_of_cycle (Cycles.unpack π)).

End Cycles.
