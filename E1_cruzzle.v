(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup B2_permutation C3_generator_chain.

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
Eval cbv in map (map Cycles.unpack) (map fst (map fst chain)).
(*
[
  [
    [[3; 1; 2; 3]];
    [[5; 6; 4; 5]];
    [[4; 1; 4]];
    [[5; 2; 5]];
    [[3; 6; 3]]
  ];
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
  ];
  [
    [[5; 3; 5]];
    [[5; 6; 5]];
    [[3; 4; 6; 3]];
    [[3; 6; 3]];
    [[5; 6; 4; 3; 5]];
    [[6; 4; 6]];
    [[5; 6; 4; 5]]
  ];
  [
    [[5; 6; 5]];
    [[5; 4; 5]];
    [[5; 6; 4; 5]]
  ];
  [
    [[5; 6; 5]]
  ]
]
*)

End Two_by_three.
