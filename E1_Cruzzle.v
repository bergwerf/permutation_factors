(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word B4_print.
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

Definition gen_names := ["e"; "h1"; "h2"; "v1"; "v2"; "v3"].
Definition gen : list perm := map Cycles.pack [
  [[1; 2; 3; 1]];
  [[4; 5; 6; 4]];
  [[1; 4; 1]];
  [[2; 5; 2]];
  [[3; 6; 3]]
].

Definition range := [1; 2; 3; 4; 5; 6].
Definition chain := SGChain.build gen range.
Definition sgs := Minkwitz.sgs 200 25 2 gen chain.

(* Print the permutations in the subgroup chain. *)
(* Eval cbv in str_join (print_hline 12) (map
  (λ gen, print_lines (map print_perm gen))
  (map fst (map fst chain))). *)

(* Print the words of the strong generating set. *)
Eval cbv in print_table "│" [" "; "─"] (
  ("" :: map print_positive range) ::
  ("" :: repeat "" (List.length range)) ::
  map (λ row, match row with (k, _, orbit) =>
    print_positive k ::
    map (λ i,
      match lookup orbit i with
      | Some (_, w) => print_word gen_names w
      | None => ""
      end)
    range
  end) sgs).
(*
│   │ 1 │ 2  │ 3       │ 4     │ 5     │ 6            │
│───│───│────│─────────│───────│───────│──────────────│
│ 1 │   │ h1 │ h1'     │ v1    │ v2h1  │ h2'v1        │
│ 2 │   │    │ v1'h1v1 │ h2'v2 │ v2    │ h2v2         │
│ 3 │   │    │         │ h2v3  │ h2'v3 │ v3           │
│ 4 │   │    │         │       │ h2    │ h2'          │
│ 5 │   │    │         │       │       │ v3'h2'v3h2v3 │
*)

(***
Solve an instance of the puzzle. Note that we first determine a word for the
following puzzle permutation, and then invert it to obtain the moves needed to
revert it back into the identity permutation.
┏━━━┳━━━┳━━━┓
┃ 5 ┃ 1 ┃ 6 ┃
┣━━━╋━━━╋━━━┫
┃ 3 ┃ 4 ┃ 2 ┃
┗━━━┻━━━┻━━━┛
Solution: v3'h2'v3'h2v1'h1'v1h1'v2'.
*)
Eval cbv in
  let π := create_perm [5; 1; 6; 3; 4; 2] in
  match Minkwitz.describe gen sgs π with
  | Some w => print_word gen_names (inv_word w)
  | None => "?"
  end.

End Two_by_three.
