(* String printing utilities. *)

From CGT Require Import A1_setup B2_perm B3_word.
Require Import Byte Ascii String DecimalString.

Local Open Scope string_scope.

Definition str_lf := String (ascii_of_byte x0a) EmptyString.
Definition str_concat l := fold_left append l "".
Definition str_padl n c s := s ++ str_concat (repeat c (n - length s)).
Fixpoint str_join sep l :=
  match l with
  | [] => ""
  | [x] => x
  | x :: l' => x ++ sep ++ str_join sep l'
  end.

Definition print_hline n := str_concat (repeat "-" n).
Definition print_lines ls := str_lf ++ str_concat (map (λ l, l ++ str_lf) ls).
Definition print_positive i := NilZero.string_of_uint (Pos.to_uint i).
Definition print_csv table := print_lines (map (str_join ",") table).

(***
Print a permutation using cycle notation.
*)

Definition print_cycle (c : Cycles.cycle) :=
  "(" ++ str_join " " (map print_positive (removelast c)) ++ ")".

Definition print_perm (π : perm) :=
  str_join " " (map print_cycle (Cycles.unpack π)).

(***
Print a word using a list of letter names.
*)

Definition print_letter (names : list string) (l : letter) :=
  match l with
  | Forward i => nth (Pos.to_nat i) names (print_positive i)
  | Inverse i => nth (Pos.to_nat i) names (print_positive i) ++ "'"
  end.

Definition print_word names w := str_concat (map (print_letter names) w).

(***
Print a table with aligned columns and column separators.
*)
Section Print_table.

Variable sep : string.
Variable padc : list string.
Variable table : list (list string).

Definition column_width i :=
  fold_left Nat.max (map (λ row, length (nth i row "")) table) O.

Definition format_table :=
  let n := fold_left Nat.max (map (@List.length _) table) O in
  let w := map (column_width) (seq 0 n) in
  map (λ row, match row with (i, cols) =>
    map (λ cell, match cell with (width, content) =>
      str_padl width (nth i padc " ") content
    end) (combine w cols)
  end) (combine (seq 0 (List.length table)) table).

Definition print_table :=
  print_lines (map (λ row, match row with (i, cols) =>
    let c := nth i padc " " in
    sep ++ c ++ str_join (c ++ sep ++ c) cols ++ c ++ sep
  end) (combine (seq 0 (List.length table)) format_table)).

End Print_table.
