(* Storing finite maps as unbalanced binary trees. *)

From permutation_solver Require Import A_setup.

Open Scope positive.

(***
Operations on positive numbers
*)

(* Reverse append i to an accumulator. *)
Fixpoint lifo (i acc : positive) :=
  match i with
  | xH => acc
  | xO i' => lifo i' (xO acc)
  | xI i' => lifo i' (xI acc)
  end.

Notation mirror i := (lifo i xH).

(***
Unbalanced binary tree

Using an unbalanced tree has several interesting advantages:
- Implementation is simpler.
- Creation does not require balancing.
- Lookup does not require key comparison.
*)

Inductive fmap := Leaf | Node (iO : option positive) (f0 f1 : fmap).

(***
Insert and lookup mappings
*)

(* Insert j at i. *)
Fixpoint insert (f : fmap) (i j : positive) :=
  match f with
  | Leaf =>
    match i with
    | xH => Node (Some j) Leaf Leaf
    | xO i' => Node None (insert Leaf i' j) Leaf
    | xI i' => Node None Leaf (insert Leaf i' j)
    end
  | Node iO f0 f1 =>
    match i with
    | xH => Node (Some j) f0 f1
    | xO i' => Node iO (insert f0 i' j) f1
    | xI i' => Node iO f0 (insert f1 i' j)
    end
  end.

(* Get the value at i. *)
Fixpoint lookup (f : fmap) (i : positive) : option positive :=
  match f with
  | Leaf => None
  | Node jO f0 f1 =>
    match i with
    | xH => jO
    | xO i' => lookup f0 i'
    | xI i' => lookup f1 i'
    end
  end.

(***
Function application
*)

Definition apply f i :=
  match lookup f i with
  | Some j => j
  | None => i
  end.

Notation "f ⋅ i" := (apply f i) (at level 5, format "f ⋅ i").

(***
Function composition
*)

(* Apply g to all mappings in f. *)
Fixpoint fmap_map (g f : fmap) :=
  match f with
  | Leaf => Leaf
  | Node (Some i) f0 f1 => Node (Some g⋅i) (fmap_map g f0) (fmap_map g f1)
  | Node None f0 f1 => Node None (fmap_map g f0) (fmap_map g f1)
  end.

(* Apply g after f. The initial input for g must be copied as gI. *)
Fixpoint compose (gI g f : fmap) {struct f} :=
  match f with
  | Leaf => g
  | Node (Some i) f0 f1 =>
    match g with
    | Leaf => Node (Some gI⋅i) (fmap_map gI f0) (fmap_map gI f1)
    | Node jO g0 g1 => Node (Some gI⋅i) (compose gI g0 f0) (compose gI g1 f1)
    end
  | Node None f0 f1 =>
    match g with
    | Leaf => Node None (fmap_map gI f0) (fmap_map gI f1)
    | Node jO g0 g1 => Node jO (compose gI g0 f0) (compose gI g1 f1)
    end
  end.

Notation "g ∘ f" := (compose g g f) (at level 50).

(***
Function inversion
*)

(* Invert a surjective map. *)
Fixpoint invert (f f_inv : fmap) (r : positive) :=
  match f with
  | Leaf => f_inv
  | Node iO f0 f1 =>
    let f_inv' := invert f0 f_inv r~0 in
    let f_inv'' := invert f1 f_inv' r~1 in
    match iO with
    | Some i => insert f_inv'' i (mirror r)
    | None => f_inv''
    end
  end.

Notation inv f := (invert f Leaf xH).

(***
Pruning

There are several advantages of pruning (removing identity mappings) trees after
composition. There is a slight advantage for lookups, but more importantly;
compositions will be faster. The inversion function we define later will also
benefit from pruning. But, this optimization is more tricky than it seems,
because pruning is quite expensive. We have to compare every mapping to its key
path, and, when recursively iterating the tree, we have to keep track of the
position of every node which requires appending bits to the end of a `positive`.

Because we will be working with permutations on the same finite domain, I think
this pruning procedure can be optimized a little by pre-computing the tree of
all identity mappings. Hence I have implemented a sifting function that removes
the mappings that are present in a given tree. We will have to determine in
practice if this sifting procedure actually provides a net speed-up.
*)

(* A pruned fmap contains no explicit identity mappings. *)
Fixpoint Pruned (f : fmap) (r : positive) :=
  match f with
  | Leaf => True
  | Node iO f0 f1 =>
    Pruned f0 r~0 /\
    Pruned f1 r~1 /\
    match iO with
    | Some i => i ≠ mirror r
    | None => True
    end
  end.

(* Remove the mappings in f that are also in s. *)
Fixpoint sift (f s : fmap) :=
  let collapse := λ (f0 f1 : fmap),
    match f0, f1 with
    | Leaf, Leaf => Leaf
    | f0', f1' => Node None f0' f1'
    end
  in match s with
  | Leaf => f
  | Node iO s0 s1 =>
    match f with
    | Leaf => Leaf
    | Node None f0 f1 => collapse (sift f0 s0) (sift f1 s1)
    | Node (Some j) f0 f1 =>
      match iO with
      | Some i =>
        if i =? j
        then collapse (sift f0 s0) (sift f1 s1)
        else Node (Some j) (sift f0 s0) (sift f1 s1)
      | None => Node (Some j) (sift f0 s0) (sift f1 s1)
      end
    end
  end.

(***
Theorems
*)

Local Ltac fmap_induction f :=
  induction f as [|jO f0 IHf0 f1 IHf1]; simpl; intros.

Lemma lookup_fmap_map_None g f i :
  lookup f i = None -> lookup (fmap_map g f) i = None.
Proof.
revert i; fmap_induction f. easy.
destruct i, jO as [j|]; simpl; try easy.
all: try apply IHf0; try apply IHf1; easy.
Qed.

Lemma lookup_compose_None gI g f i :
  lookup f i = None -> lookup (compose gI g f) i = lookup g i.
Proof.
revert g i; fmap_induction f. easy.
destruct jO as [j|], g, i; simpl; try easy.
1,2,5,6: apply lookup_fmap_map_None, H.
all: try rewrite IHf1; try rewrite IHf0; easy.
Qed.

Lemma lookup_fmap_map_Some g f i j :
  lookup f i = Some j -> lookup (fmap_map g f) i = Some g⋅j.
Proof.
revert g i; fmap_induction f. easy.
destruct jO as [j'|], i; simpl; try congruence.
all: try apply IHf0; try apply IHf1; easy.
Qed.

Lemma lookup_compose_Some gI g f i j :
  lookup f i = Some j -> lookup (compose gI g f) i = Some gI⋅j.
Proof.
revert g i; induction f as [|jO f0 IHf0 f1 IHf1]; simpl; intros. easy.
destruct jO as [j'|], g, i; simpl; try congruence.
all: try apply lookup_fmap_map_Some; try apply IHf0; try apply IHf1; easy.
Qed.

Corollary apply_compose g f i :
  (g ∘ f)⋅i = g⋅(f⋅i).
Proof.
unfold apply; destruct (lookup f i) as [j|] eqn:H.
erewrite lookup_compose_Some; easy.
erewrite lookup_compose_None; easy.
Qed.
