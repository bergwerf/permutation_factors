(* Permutations as unbalanced binary trees (fmap). *)

From permutation_solver Require Import A_setup B1_fmap.

(***
Permutations

Using an unbalanced tree (fmap) to store permutations outperforms a balanced
tree because permutation indices are relatively small (for Rubik's cube we have
48 indices). Of course not all finite maps represent a permutation.

There are several equivalent ways to describe a valid permutation:
- A permutation is a bijective function from a finite set to itself.
- A permutation is the result of composing a list of transpositions.
- The node-numbers and ident-numbers of a permutation are all unique.

Next we want to describe what it means for a subset of fmap to describe a
permutation group. Therefore it has to follow the usual group axioms:
1. Composition of any three elements in the set is associative.
2. The set contains the identity permutation.
3. The set contains the inverse of any permutation.
*)

Notation "'perm'" := (fmap).
