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
Section Unbalanced_binary_tree.

Variable V : Type.

Inductive fmap := Leaf | Node (vO : option V) (f0 f1 : fmap).

(***
Insert and lookup mappings
*)

(* Create a map that only maps i to j. *)
Fixpoint create (i : positive) (v : V) :=
  match i with
  | xH => Node (Some v) Leaf Leaf
  | xO i' => Node None (create i' v) Leaf
  | xI i' => Node None Leaf (create i' v)
  end.

(* Insert j at i. *)
Fixpoint insert (f : fmap) (i : positive) (v : V) :=
  match f with
  | Leaf => create i v
  | Node vO f0 f1 =>
    match i with
    | xH => Node (Some v) f0 f1
    | xO i' => Node vO (insert f0 i' v) f1
    | xI i' => Node vO f0 (insert f1 i' v)
    end
  end.

(* Get the value at i. *)
Fixpoint lookup (f : fmap) (i : positive) :=
  match f with
  | Leaf => None
  | Node vO f0 f1 =>
    match i with
    | xH => vO
    | xO i' => lookup f0 i'
    | xI i' => lookup f1 i'
    end
  end.

End Unbalanced_binary_tree.

Arguments Leaf {_}.
Arguments Node {_}.
Arguments create {_}.
Arguments insert {_}.
Arguments lookup {_}.

Notation ffun := (fmap positive).

(***
Function application
*)

Definition apply (f : ffun) i :=
  match lookup f i with
  | Some j => j
  | None => i
  end.

Notation "f ⋅ i" := (apply f i) (at level 5, format "f ⋅ i").

(***
Function composition
*)

(* Apply g to all mappings in f. *)
Fixpoint map_ffun (g f : ffun) :=
  match f with
  | Leaf => Leaf
  | Node (Some i) f0 f1 => Node (Some g⋅i) (map_ffun g f0) (map_ffun g f1)
  | Node None f0 f1 => Node None (map_ffun g f0) (map_ffun g f1)
  end.

(* Apply g after f. The initial input for g must be copied as gI. *)
Fixpoint compose (gI g f : ffun) {struct f} :=
  match f with
  | Leaf => g
  | Node (Some i) f0 f1 =>
    match g with
    | Leaf => Node (Some gI⋅i) (map_ffun gI f0) (map_ffun gI f1)
    | Node jO g0 g1 => Node (Some gI⋅i) (compose gI g0 f0) (compose gI g1 f1)
    end
  | Node None f0 f1 =>
    match g with
    | Leaf => Node None (map_ffun gI f0) (map_ffun gI f1)
    | Node jO g0 g1 => Node jO (compose gI g0 f0) (compose gI g1 f1)
    end
  end.

Notation "g ∘ f" := (compose g g f) (at level 50).

(***
Function inversion
*)

(* Invert a surjective map. *)
Fixpoint invert (f f_inv : ffun) (r : positive) :=
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

(* A pruned function tree contains no explicit identity mappings. *)
Fixpoint Pruned (f : ffun) (r : positive) :=
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
Fixpoint sift (f s : ffun) :=
  let collapse := λ (f0 f1 : ffun),
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

Lemma lookup_create_eq {V} i (v : V) : lookup (create i v) i = Some v.
Proof. induction i; easy. Qed.

Lemma lookup_create_neq {V} i j (v : V) :
  i ≠ j -> lookup (create i v) j = None.
Proof.
revert j; induction i; simpl; intros; destruct j.
all: try easy; apply IHi; congruence.
Qed.

Theorem lookup_insert_eq {V} f i (v : V) :
  lookup (insert f i v) i = Some v.
Proof.
revert i; fmap_induction f.
apply lookup_create_eq.
destruct i; simpl; easy.
Qed.

Theorem lookup_insert_neq {V} f i j (v : V) :
  i ≠ j -> lookup (insert f i v) j = lookup f j.
Proof.
revert i j; fmap_induction f.
apply lookup_create_neq, H.
destruct i, j; simpl; try easy.
apply IHf1; congruence.
apply IHf0; congruence.
Qed.

Theorem lookup_insert {V} f i j (v : V) :
  lookup (insert f i v) j = if i =? j then Some v else lookup f j.
Proof.
destruct (i =? j) eqn:E; [apply Pos.eqb_eq in E|apply Pos.eqb_neq in E].
subst; apply lookup_insert_eq. apply lookup_insert_neq, E.
Qed.

Lemma lookup_map_ffun_None g f i :
  lookup f i = None -> lookup (map_ffun g f) i = None.
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
1,2,5,6: apply lookup_map_ffun_None, H.
all: try rewrite IHf1; try rewrite IHf0; easy.
Qed.

Lemma lookup_map_ffun_Some g f i j :
  lookup f i = Some j -> lookup (map_ffun g f) i = Some g⋅j.
Proof.
revert g i; fmap_induction f. easy.
destruct jO as [j'|], i; simpl; try congruence.
all: try apply IHf0; try apply IHf1; easy.
Qed.

Lemma lookup_compose_Some gI g f i j :
  lookup f i = Some j -> lookup (compose gI g f) i = Some gI⋅j.
Proof.
revert g i; fmap_induction f. easy.
destruct jO as [j'|], g, i; simpl; try congruence.
all: try apply lookup_map_ffun_Some; try apply IHf0; try apply IHf1; easy.
Qed.

Theorem apply_compose g f i :
  (g ∘ f)⋅i = g⋅(f⋅i).
Proof.
unfold apply; destruct (lookup f i) as [j|] eqn:H.
erewrite lookup_compose_Some; easy.
erewrite lookup_compose_None; easy.
Qed.

Lemma lookup_invert_Some f f_inv r i j :
  lookup f_inv j = None ->
  lookup (invert f f_inv r) j = Some (lifo r i) ->
  lookup f i = Some j.
Proof.
revert f_inv r i; fmap_induction f. congruence.
Admitted.
