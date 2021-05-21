(* Definition and manipulation of generator words. *)

From CGT Require Import A1_setup B1_fmap B2_perm.

(***
:: Words ::

We want to express permutations as words in an alphabet of generators. In this
file we implement two types of words: (1) Lists of permutations which are
contained in a list of generators. These words are used in proofs. (2) Lists of
letters with positive indices. These words are used for the strong generating
set filling algorithm. The inverse of a generator is part of the alphabet
because inverting words is essential. For fast application of these words we
store generators and their inverses in a lookup map.
*)

(* Apply a list of permutations to index i. *)
Notation apply' w i := (fold_right apply i w).

(* Compose a list of permutations. *)
Notation compose' w := (fold_right (λ σ π, σ ∘ π) ident w).

(***
:: Bounded length of orbit words ::

The orbit of k consists of all points that are reachable from k using a
generator. We can imagine all moving points (the objects that are permuted) as
nodes in a graph which are connected by permutations. An edge between two nodes
may be labelled with multiple permutations, and one permutation might occur at
multiple edges. Every word forms a path in this graph, connecting different
pairs of points. We claim that the orbit of k is fully determined when all words
with length at most the number of points in the graph have been accounted for.

Using the pigeon-hole principle we can determine for any two points i and j; if
i and j are connected by some word, then there exists a connecting word between
them with length at most the total number of points in the graph. Furthermore,
we can make sure that this word never visits the same point twice.
*)

(* The points visited by word w starting at point i. *)
Fixpoint visited_points w i :=
  match w with
  | [] => []
  | σ :: w' => let j := σ⋅i in j :: visited_points w' j
  end.

(* Remove cycles from a connecting word. *)
Theorem short_orbit_word w i :
  ∃w', w' ⊆ w /\ NoDup (visited_points w' i) /\ apply' w' i = apply' w i.
Proof.
Admitted.

(* Letters for invertible words and fast operations. *)
Inductive letter :=
  | Forward (x : positive)
  | Inverse (x : positive).

Notation word := (list letter).

(* Compare two letters. *)
Definition eqb_letter (a b : letter) :=
  match a, b with
  | Forward i, Forward j => i =? j
  | Inverse j, Inverse i => i =? j
  | _, _ => false
  end.

(* Invert a letter. *)
Definition inv_letter (a : letter) :=
  match a with
  | Forward i => Inverse i
  | Inverse i => Forward i
  end.

(* Invert a word. *)
Definition inv_word (w : word) := rev (map inv_letter w).

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
Fixpoint next_word (reset : positive) (w : word) :=
  match w with
  | [] => [Forward reset]
  | Forward 1 :: w' => Inverse reset :: w'
  | Forward i :: w' => Forward (Pos.pred i) :: w'
  | Inverse 1 :: w' => Forward reset :: next_word reset w'
  | Inverse i :: w' => Inverse (Pos.pred i) :: w'
  end.

(***
:: Word application ::

When building words we can compose the generators corresponding to each letter
to find the permutations they represent. But composition is expensive, and in
the SGS (strong generating set) building algorithm by Minkwitz we only need to
do specific lookups in the resulting permutations. I expect that the average
word length will be short enough such that composition does not have an
advantage over directly applying the generators one-by-one.
*)
Definition generators := fmap perm × fmap perm.

(* Apply a word to a number. *)
Fixpoint apply_word (gen : generators) (w : word) (i : positive) :=
  match w with
  | [] => i
  | Forward x :: w' => (lookup (fst gen) x ?? ident)⋅(apply_word gen w' i)
  | Inverse x :: w' => (lookup (snd gen) x ?? ident)⋅(apply_word gen w' i)
  end.

(* Build fast lookup map for a generating set. *)
Definition prepare_generators (gen : list perm) : generators :=
  fold_left (λ dst src, (
    insert (fst dst) (fst src) (snd src),
    insert (snd dst) (fst src) (inv (snd src))))
    (combine (map Pos.of_nat (seq 1 (length gen))) gen)
    (Leaf, Leaf).

(***
I find it inelegant to repeatedly produce natural numbers for list length
comparison, so I created these optimized functions.
*)

(* Optimized version of `length l <=? n`. *)
Fixpoint length_le_nat {X} (l : list X) n :=
  match l with
  | [] => true
  | _ :: l' =>
    match n with
    | O => false
    | S m => length_le_nat l' m
    end
  end.

(* Optimized version of `length l1 <? length l2`. *)
Fixpoint length_lt_length {X} (l1 l2 : list X) :=
  match l2 with
  | [] => false
  | _ :: l2' =>
    match l1 with
    | [] => true
    | _ :: l1' => length_lt_length l1' l2'
    end
  end.
