(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup B1_finite_map B2_permutation.
From CGT Require Import C1_Schreier_vector C2_Sims_filter.

(*
┏━━━┳━━━┳━━━┓
┃ 1 ┃ 2 ┃ 3 ┃
┣━━━╋━━━╋━━━┫
┃ 4 ┃ 5 ┃ 6 ┃
┗━━━┻━━━┻━━━┛
*)
Section Two_by_three.

Definition generator0 : list perm := map Cycles.pack [
  [[1; 2; 3; 1]];
  [[4; 5; 6; 4]];
  [[1; 4; 1]];
  [[2; 5; 2]];
  [[3; 6; 3]]
].

Definition sieve4 := identity_sieve 4 xH.
Definition vector1 := Schreier.build generator0 1 6.
Definition generator1 := Schreier.generator generator0 1 vector1.
Definition generator1' := Sims.filter sieve4 6 generator1.

Eval lazy in (map Cycles.unpack generator1').
(*
[
  [[5; 6; 2; 4; 5]];
  [[6; 2; 6]; [5; 4; 5]];
  [[5; 2; 5]];
  [[5; 6; 3; 2; 4; 5]];
  [[3; 4; 2; 3]];
  [[3; 6; 2; 3]];
  [[5; 2; 3; 5]];
  [[6; 4; 6]];
  [[5; 6; 4; 5]]
]
*)

End Two_by_three.
