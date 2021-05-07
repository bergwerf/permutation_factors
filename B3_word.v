(* Definition and manipulation of generator words. *)

From CGT Require Import A1_setup B1_fmap B2_perm.

(* Letters to build permutations (positive index for fast comparison). *)
Inductive letter :=
  | Forward (i : positive)
  | Inverse (i : positive).

(* Compare two generator letters. *)
Definition letter_eqb (a b : letter) :=
  match a, b with
  | Forward i, Forward j => i =? j
  | Inverse j, Inverse i => i =? j
  | _, _ => false
  end.

(* Invert a generator letter. *)
Definition letter_inv (a : letter) :=
  match a with
  | Forward i => Inverse i
  | Inverse i => Forward i
  end.

(* Invert a word. *)
Definition word_inv (word : list letter) := rev (map letter_inv word).

(* Produce a permutation from a word (generator inverses are not cached). *)
Fixpoint generate (gen : list perm) (word : list letter) :=
  match word with
  | [] => ident
  | Forward i :: w => nth (Pos.to_nat i) gen ident ∘ generate gen w
  | Inverse i :: w => inv (nth (Pos.to_nat i) gen ident) ∘ generate gen w
  end.

(* Remove redundant permutations from a word. *)
Fixpoint reduce (stack word : list letter) :=
  match word with
  | [] => rev stack
  | a :: w =>
    match stack with
    | [] => reduce [a] w
    | b :: s =>
      if letter_eqb a (letter_inv b)
      then reduce s w
      else reduce (a :: stack) w
    end
  end.

(* Generate all words of length n. *)
Fixpoint generate_words (alphabet : list letter) n : list (list letter) :=
  match n with
  | O => [[]]
  | S m => map (λ p, fst p :: snd p)
    (list_prod alphabet (generate_words alphabet m))
  end.
