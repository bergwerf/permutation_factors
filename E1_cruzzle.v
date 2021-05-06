(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup A2_print B2_permutation C3_generator_chain.

(*
┏━━━┳━━━┳━━━┓
┃ 1 ┃ 2 ┃ 3 ┃
┣━━━╋━━━╋━━━┫
┃ 4 ┃ 5 ┃ 6 ┃
┗━━━┻━━━┻━━━┛
*)
Section Two_by_three.

Definition generator : list perm := map Cycles.pack [
  [[1; 2; 3; 1]];
  [[4; 5; 6; 4]];
  [[1; 4; 1]];
  [[2; 5; 2]];
  [[3; 6; 3]]
].

Definition chain := SGChain.build generator [1; 2; 3; 4; 5; 6].

Eval cbv in str_join (str_hline 12) (map
  (λ gen, str_lines (map Cycles.print gen))
  (map fst (map fst chain))).
(*
(3 1 2)
(5 6 4)
(4 1)
(5 2)
(3 6)
------------
(5 6 2 4)
(6 2) (5 4)
(5 2)
(5 6 3 2 4)
(3 4 2)
(3 6 2)
(5 2 3)
(6 4)
(5 6 4)
------------
(5 3)
(5 6)
(3 4 6)
(3 6)
(5 6 4 3)
(6 4)
(5 6 4)
------------
(5 6)
(5 4)
(5 6 4)
------------
(5 6)
*)

End Two_by_three.
