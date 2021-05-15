(* Rubik's cube. *)

From CGT Require Import A1_setup B1_fmap B2_perm B3_word B4_print.
From CGT Require Import C3_subgroup_chain D1_word_search.

Require Import String.
Local Open Scope string_scope.

(***
:: Rubiks' cube ::

Here we implement the permutations of Rubik's cube, and show how we can solve an
instance of the cube. We use the same notation and face numbering as ruwix.com
(see the doc folder). Although central cells do not need a number (they remain
fixed), we reserve a number for them anyway for convenience (to exactly follow
the numbering given in the doc folder).
*)
Module Rubiks_cube.

(*
  \  i | j | k  /
   ┏━━━┳━━━┳━━━┓
 t ┃ a ┃ b ┃ c ┃ l
---┣━━━╋━━━╋━━━┫---
 s ┃ h ┃   ┃ d ┃ m
---┣━━━╋━━━╋━━━┫---
 r ┃ g ┃ f ┃ e ┃ n
   ┗━━━┻━━━┻━━━┛
  /  q | p | o  \
*)
Definition rotation (a b c d e f g h i j k l m n o p q r s t : positive) := [
  [a; g; e; c; a]; [b; h; f; d; b];
  [i; r; o; l; i]; [j; s; p; m; j]; [k; t; q; n; k]
].

Definition gen_names := ["e"; "U"; "L"; "F"; "R"; "B"; "D"].
Definition gen : list perm := map Cycles.pack [
  rotation 01 02 03 06 09 08 07 04   39 38 37   30 29 28   21 20 19   12 11 10;
  rotation 10 11 12 15 18 17 16 13   01 04 07   19 22 25   46 49 52   45 42 39;
  rotation 19 20 21 24 27 26 25 22   07 08 09   28 31 34   48 47 46   18 15 12;
  rotation 28 29 30 33 36 35 34 31   09 06 03   37 40 43   54 51 48   27 24 21;
  rotation 37 38 39 42 45 44 43 40   03 02 01   10 13 16   52 53 54   36 33 30;
  rotation 46 47 48 51 54 53 52 49   25 26 27   34 35 36   43 44 45   16 17 18
].

End Rubiks_cube.
