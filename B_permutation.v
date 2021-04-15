(* Storing permutations as unbalanced binary trees. *)

From permutation_solver Require Import A_setup.

(***
Using an unbalanced tree has several interesting advantages:
- Implementation is simpler.
- Creation does not require balancing.
- Lookup does not require key comparison.
- Permutation indices are relatively small (n = 48 for Rubik's cube)
*)

Inductive perm := Stub | Node (i : positive) (l r : perm).

(***
A mapping defined using the `perm` type is not automatically a permutation.
There are several equivalent ways to describe a valid permutation:
- A permutation is the result of composing a list of transpositions.
- The leaf-numbers and stub-numbers of a permutation are all unique.
*)

(* Lookup i in π. The input index must be repeated for the Stub case. *)
Fixpoint lookup (π : perm) (i : positive) : positive -> positive :=
  match π with
  | Stub => λ j, j
  | Node j πl πr =>
    match i with
    | xH => λ _, j
    | xO i' => lookup πl i'
    | xI i' => lookup πr i'
    end
  end.

Notation "π ` i" := (lookup π i i) (at level 50, format "π ` i").

(* Apply τ after π. The initial τ permutation must be copied. *)
Fixpoint compose (τ0 τ π : perm) :=
  match π with
  | Stub => τ
  | Node j πl πr =>
    match τ with
    | Stub => Node (τ0`j) πl πr
    | Node _ τl τr => Node (τ0`j) (compose τ0 τl πl) (compose τ0 τr πr)
    end
  end.

(* Prune identity branches at sub-branch i. *)
Fixpoint prune (π : perm) (i : positive) :=
  match π with
  | Stub => Stub
  | Node j πl πr =>
    match prune πl (xO i), prune πr (xI i) with
    | Stub, Stub => if Pos.eqb i j then Stub else Node j Stub Stub
    | πl', πr' => Node j πl' πr'
    end
  end.

Notation "τ ∘ π" := (prune (compose τ τ π) xH) (at level 50).

(***
First we want to prove that the above operations behave as expected:
- Application after composition is equal to double application.
- Composition of two permutations results in a permutation.

If we have established that our operations are looking good, we want to really
establish that composition of permutation forms a group:
- Composition is associative (the order of operations is irrelevant).
- Composition with the identity element is identical.
- Every permutation has an inverse.
*)
