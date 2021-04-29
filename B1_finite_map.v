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

Inductive fmap := Leaf | Node (val : option V) (fO fI : fmap).

(***
Insert and lookup mappings
*)

(* Create a map that only maps key to val. *)
Fixpoint create (key : positive) (val : V) :=
  match key with
  | xH => Node (Some val) Leaf Leaf
  | xO k => Node None (create k val) Leaf
  | xI k => Node None Leaf (create k val)
  end.

(* Insert val at key. *)
Fixpoint insert (f : fmap) (key : positive) (val : V) :=
  match f with
  | Leaf => create key val
  | Node v fO fI =>
    match key with
    | xH => Node (Some val) fO fI
    | xO k => Node v (insert fO k val) fI
    | xI k => Node v fO (insert fI k val)
    end
  end.

(* Get the value at key. *)
Fixpoint lookup (f : fmap) (key : positive) :=
  match f with
  | Leaf => None
  | Node val fO fI =>
    match key with
    | xH => val
    | xO k => lookup fO k
    | xI k => lookup fI k
    end
  end.

(* Retrieve all values. *)
Fixpoint values (f : fmap) :=
  match f with
  | Leaf => []
  | Node None fO fI => values fO ++ values fI
  | Node (Some v) fO fI => v :: values fO ++ values fI
  end.

End Unbalanced_binary_tree.

Arguments Leaf {_}.
Arguments Node {_}.
Arguments create {_}.
Arguments insert {_}.
Arguments lookup {_}.
Arguments values {_}.

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
  | Node (Some i) fO fI => Node (Some g⋅i) (map_ffun g fO) (map_ffun g fI)
  | Node None fO fI => Node None (map_ffun g fO) (map_ffun g fI)
  end.

(* Apply g after f. The initial input for g must be copied as gI. *)
Fixpoint compose (gI g f : ffun) {struct f} :=
  match f with
  | Leaf => g
  | Node (Some i) fO fI =>
    match g with
    | Leaf => Node (Some gI⋅i) (map_ffun gI fO) (map_ffun gI fI)
    | Node jO g0 g1 => Node (Some gI⋅i) (compose gI g0 fO) (compose gI g1 fI)
    end
  | Node None fO fI =>
    match g with
    | Leaf => Node None (map_ffun gI fO) (map_ffun gI fI)
    | Node jO g0 g1 => Node jO (compose gI g0 fO) (compose gI g1 fI)
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
  | Node i_opt fO fI =>
    let f_inv' := invert fO f_inv r~0 in
    let f_inv'' := invert fI f_inv' r~1 in
    match i_opt with
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
  | Node i_opt fO fI =>
    Pruned fO r~0 /\
    Pruned fI r~1 /\
    match i_opt with
    | Some i => i ≠ mirror r
    | None => True
    end
  end.

(* Remove the mappings in f that are also in s. *)
Fixpoint sift (f s : ffun) :=
  let collapse := λ (fO fI : ffun),
    match fO, fI with
    | Leaf, Leaf => Leaf
    | fO', fI' => Node None fO' fI'
    end
  in match s with
  | Leaf => f
  | Node i_opt s0 s1 =>
    match f with
    | Leaf => Leaf
    | Node None fO fI => collapse (sift fO s0) (sift fI s1)
    | Node (Some j) fO fI =>
      match i_opt with
      | Some i =>
        if i =? j
        then collapse (sift fO s0) (sift fI s1)
        else Node (Some j) (sift fO s0) (sift fI s1)
      | None => Node (Some j) (sift fO s0) (sift fI s1)
      end
    end
  end.

(***
Theorems
*)

Local Ltac fmap_induction f :=
  induction f as [|j_opt fO IHfO fI IHfI]; simpl; intros.

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
apply IHfI; congruence.
apply IHfO; congruence.
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
destruct i, j_opt as [j|]; simpl; try easy.
all: try apply IHfO; try apply IHfI; easy.
Qed.

Lemma lookup_compose_None gI g f i :
  lookup f i = None -> lookup (compose gI g f) i = lookup g i.
Proof.
revert g i; fmap_induction f. easy.
destruct j_opt as [j|], g, i; simpl; try easy.
1,2,5,6: apply lookup_map_ffun_None, H.
all: try rewrite IHfI; try rewrite IHfO; easy.
Qed.

Lemma lookup_map_ffun_Some g f i j :
  lookup f i = Some j -> lookup (map_ffun g f) i = Some g⋅j.
Proof.
revert g i; fmap_induction f. easy.
destruct j_opt as [j'|], i; simpl; try congruence.
all: try apply IHfO; try apply IHfI; easy.
Qed.

Lemma lookup_compose_Some gI g f i j :
  lookup f i = Some j -> lookup (compose gI g f) i = Some gI⋅j.
Proof.
revert g i; fmap_induction f. easy.
destruct j_opt as [j'|], g, i; simpl; try congruence.
all: try apply lookup_map_ffun_Some; try apply IHfO; try apply IHfI; easy.
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
