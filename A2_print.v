(* String printing utilities. *)

From CGT Require Import A1_setup.
Require Import Byte Ascii String DecimalString.
Export String.

Local Open Scope string_scope.

Definition str_concat l := fold_left append l "".
Definition str_lf := String (ascii_of_byte x0a) EmptyString.
Definition str_hline n := str_concat (repeat "-" n).
Definition str_lines ls := str_lf ++ str_concat (map (λ l, l ++ str_lf) ls).
Definition str_itoa i := NilZero.string_of_uint (Pos.to_uint i).

Fixpoint str_join sep l :=
  match l with
  | [] => ""
  | [x] => x
  | x :: l' => x ++ sep ++ str_join sep l'
  end.
