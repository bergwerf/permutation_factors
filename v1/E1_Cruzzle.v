(* The Cruzzle puzzle. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word B5_print.
From CGT Require Import C3_subgroup_chain D1_word_search.

Require Import String.
Local Open Scope string_scope.

(*
    ↑   ↑   ↑
  ┏━━━┳━━━┳━━━┓
← ┃ 1 ┃ 2 ┃ 3 ┃
  ┣━━━╋━━━╋━━━┫
← ┃ 4 ┃ 5 ┃ 6 ┃
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

(* Build a strong generating set. *)
Definition range := [1; 2; 3; 4; 5; 6].
Definition chain := SGChain.build gen range.
Definition table := SGS.initialize (SGS.save_orbits chain).
Definition sgs := SGS.fill table gen 200 25 2.

(* Print the subgroup chain. *)
(* Eval cbv in str_join (print_hline 12) (map
  (λ gen, print_lines (map print_perm gen))
  (map fst (map fst chain))). *)

(* Show that all orbits are filled. *)
Compute SGS.complete sgs.

(* Print it as a table. *)
Compute print_table "│" [" "; "─"] (
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
│   │ 1 │ 2   │ 3       │ 4     │ 5     │ 6            │
│───│───│─────│─────────│───────│───────│──────────────│
│ 1 │   │ h1' │ h1      │ v1'   │ v1h2' │ v1h2         │
│ 2 │   │     │ v1h1'v1 │ v2h2  │ v2'   │ v2h2'        │
│ 3 │   │     │         │ v3h2' │ v3h2  │ v3'          │
│ 4 │   │     │         │       │ h2'   │ h2           │
│ 5 │   │     │         │       │       │ v2h2v2h2'v2' │
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
Solution: h2v3'v2h2v1h2'.
*)
Compute
  let π := create_perm [5; 1; 6; 3; 4; 2] in
  match SGS.factorize sgs gen π with
  | Some w => print_word gen_names (inv_word w)
  | None => "?"
  end.

End Two_by_three.
