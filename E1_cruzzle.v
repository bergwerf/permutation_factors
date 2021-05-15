(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup B1_fmap B2_perm B4_print.
From CGT Require Import C3_subgroup_chain D1_word_search.

Require Import String.
Local Open Scope string_scope.

(*
┏━━━┳━━━┳━━━┓
┃ 1 ┃ 2 ┃ 3 ┃
┣━━━╋━━━╋━━━┫
┃ 4 ┃ 5 ┃ 6 ┃
┗━━━┻━━━┻━━━┛
*)
Section Two_by_three.

Definition gen : list perm := map Cycles.pack [
  [[1; 2; 3; 1]];
  [[4; 5; 6; 4]];
  [[1; 4; 1]];
  [[2; 5; 2]];
  [[3; 6; 3]]
].

Definition gen_names : list string := [
  "e"; "H1"; "H2"; "V1"; "V2"; "V3"
].

Definition range := [1; 2; 3; 4; 5; 6].
Definition chain := SGChain.build gen range.
Definition sgs := Minkwitz.sgs 100 25 4 gen chain.

(* Print the permutations in the subgroup chain. *)
Eval cbv in str_join (print_hline 12) (map
  (λ gen, print_lines (map print_perm gen))
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

(* Print the words of the strong generating set. *)
Eval cbv in print_table "│" [" "; "─"] (
  ("" :: map print_positive range) ::
  ("" :: repeat "" (List.length range)) ::
  map (λ row, match row with (k, _, orbit) =>
    print_positive k ::
    map (λ i,
      match lookup orbit i with
      | None => ""
      | Some (_, w) => print_word gen_names w
      end)
    range
  end) sgs).
(*
│   │ 1 │ 2   │ 3         │ 4         │ 5         │ 6               │
│───│───│─────│───────────│───────────│───────────│─────────────────│
│ 1 │   │ H1+ │ H1-       │ V1+       │ H1+V2+    │ H1-V3+          │
│ 2 │   │     │ V1+H1+V1- │ V1+H1-V1- │ V2+       │ V2+H2+          │
│ 3 │   │     │           │ V3+H2+    │ H1-V2+H1+ │ V3+             │
│ 4 │   │     │           │           │ H2+       │ H2-             │
│ 5 │   │     │           │           │           │ V3+H2+V3+H2-V3- │
*)

End Two_by_three.
