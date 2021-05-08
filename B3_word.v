(* Definition and manipulation of generator words. *)

From CGT Require Import A1_setup B1_fmap B2_perm.

(* Letters to build permutations. *)
Inductive letter :=
  | Forward (i : nat)
  | Inverse (i : nat).

Notation word := (list letter).

(* Compare two generator letters. *)
Definition eqb_letter (a b : letter) :=
  match a, b with
  | Forward i, Forward j => (i =? j)%nat
  | Inverse j, Inverse i => (i =? j)%nat
  | _, _ => false
  end.

(* Invert a generator letter. *)
Definition inv_letter (a : letter) :=
  match a with
  | Forward i => Inverse i
  | Inverse i => Forward i
  end.

(* Invert a word. *)
Definition inv_word (w : word) := rev (map inv_letter w).

(* Produce a permutation from a word (generator inverses are not cached). *)
Fixpoint generate (gen : list perm) (w : word) :=
  match w with
  | [] => ident
  | Forward i :: w' => nth i gen ident ∘ generate gen w'
  | Inverse i :: w' => inv (nth i gen ident) ∘ generate gen w'
  end.

(* Remove redundant permutations from a word. *)
Fixpoint reduce (stack w : word) :=
  match w with
  | [] => rev stack
  | a :: w' =>
    match stack with
    | [] => reduce [a] w'
    | b :: s =>
      if eqb_letter a (inv_letter b)
      then reduce s w'
      else reduce (a :: stack) w'
    end
  end.

(* Go to the next word given a reset index. *)
Fixpoint next_word (n : nat) (w : word) :=
  match w with
  | [] => [Forward n]
  | Forward (S i) :: w' => Forward i :: w'
  | Forward O :: w'     => Inverse n :: w'
  | Inverse (S i) :: w' => Inverse i :: w'
  | Inverse O :: w'     => Forward n :: next_word n w'
  end.
