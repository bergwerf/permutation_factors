(* Storing finite maps as unbalanced binary trees. *)

From CGT Require Import A1_setup.
Require Import RelationClasses.

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
:: Unbalanced binary tree ::

In this project we need lookup maps for several purposes such as storing
permutations and storing indexed tables with fast lookups. The most logical way
to do this in Coq is to build a radix-2 lookup tree, since a single iteration
through the key is enough to retrieve an element (a O(n) lookup). Note that the
permutations, vectors, and tables we implement using this datastructure could be
implemented using fixed arrays in a non-functional language, this would make the
whole algorithm significantly faster, but not by orders of magnitude. Also note
that existing Coq libraries such as std++ already provide radix-2 lookup trees,
I just decided to construct them from scratch.
*)
Section Unbalanced_binary_tree.

Variable V : Type.

Inductive fmap := Leaf | Node (val : option V) (fO fI : fmap).

(***
Generic operations
*)

(* Count the number of entries. *)
Fixpoint size (f : fmap) :=
  match f with
  | Leaf => O
  | Node None fO fI => (size fO + size fI)%nat
  | Node (Some v) fO fI => S (size fO + size fI)%nat
  end.

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

(* Retrieve all entries. *)
Fixpoint entries (f : fmap) (r : positive) :=
  match f with
  | Leaf => []
  | Node None fO fI => entries fO r~0 ++ entries fI r~1
  | Node (Some v) fO fI => (mirror r, v) :: entries fO r~0 ++ entries fI r~1
  end.

(* Apply a transformation to all values. *)
Fixpoint mapval (t : V -> V) (f : fmap) :=
  match f with
  | Leaf => Leaf
  | Node (Some v) fO fI => Node (Some (t v)) (mapval t fO) (mapval t fI)
  | Node None fO fI => Node None (mapval t fO) (mapval t fI)
  end.

End Unbalanced_binary_tree.

Arguments Leaf {_}.
Arguments Node {_}.
Arguments size {_}.
Arguments create {_}.
Arguments insert {_}.
Arguments lookup {_}.
Arguments values {_}.
Arguments entries {_}.
Arguments mapval {_}.

Notation Defined f key := (lookup f key ≠ None).
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
Definition Equivalent f g := ∀i, f⋅i = g⋅i.
Notation "f == g" := (Equivalent f g) (at level 60).

(***
Function composition
*)

(* Apply g after f. The initial input for g must be copied as gI. *)
Fixpoint compose (gI g f : ffun) {struct f} :=
  let map_apply g f := mapval (apply g) f in
  match f with
  | Leaf => g
  | Node (Some i) fO fI =>
    match g with
    | Leaf => Node (Some gI⋅i) (map_apply gI fO) (map_apply gI fI)
    | Node jO g0 g1 => Node (Some gI⋅i) (compose gI g0 fO) (compose gI g1 fI)
    end
  | Node None fO fI =>
    match g with
    | Leaf => Node None (map_apply gI fO) (map_apply gI fI)
    | Node jO g0 g1 => Node jO (compose gI g0 fO) (compose gI g1 fI)
    end
  end.

Notation "g ∘ f" := (compose g g f) (at level 50).

(***
Function inversion
*)

Definition inv f :=
  fold_left (λ f_inv e, insert f_inv (snd e) (fst e)) (entries f xH) Leaf.

(***
Union of the range of a list of functions.
*)

Definition put i f := insert f i i.
Definition union_range fs := fold_right put Leaf (flat_map values fs).

(***
:: Pruning ::

There are several advantages of pruning (removing identity mappings) trees after
composition. There is a slight advantage for lookups, but more importantly;
future compositions will be faster. The inversion function we define later will
also benefit from pruning. But, this optimization is more tricky than it seems,
because pruning is quite expensive. We have to compare every mapping to its key
path, and, when recursively iterating the tree, we have to keep track of the
position of every node which requires appending bits to the end of a `positive`.

Because we will be working with permutations on the same finite domain, I think
this pruning procedure can be optimized a little by pre-computing the tree of
all identity mappings. Hence I have implemented a sifting function that removes
the mappings that are present in a given sieve. We will have to determine in
practice if pruning actually provides a net speed-up.

Note that pruning is a straightforward method to determine if a given map is an
identity function. This is used in the Sims filter, which is therefore a natural
point for pruning. For theorem proving we use slower pruning (without a sieve)
since it turns every function into a canonical form.
*)

(* A pruned function tree contains no explicit identity mappings. *)
Fixpoint Pruned (r : positive) (f : ffun) :=
  match f with
  | Leaf => True
  | Node i_opt fO fI =>
    Pruned r~0 fO /\
    Pruned r~1 fI /\
    match i_opt with
    | Some i => i ≠ mirror r
    | None => True
    end
  end.

(* Remove identity mappings from f. *)
Fixpoint prune (r : positive) (f : ffun) :=
  let collapse := λ (fO fI : ffun),
    match fO, fI with
    | Leaf, Leaf => Leaf
    | fO', fI' => Node None fO' fI'
    end
  in match f with
  | Leaf => Leaf
  | Node None fO fI => collapse (prune r~0 fO) (prune r~1 fI)
  | Node (Some i) fO fI =>
    if i =? mirror r
    then collapse (prune r~0 fO) (prune r~1 fI)
    else Node (Some i) (prune r~0 fO) (prune r~1 fI)
  end.

(* Remove mappings in f that are also in s. *)
Fixpoint sift (sieve f : ffun) :=
  let collapse := λ (fO fI : ffun),
    match fO, fI with
    | Leaf, Leaf => Leaf
    | fO', fI' => Node None fO' fI'
    end
  in match sieve with
  | Leaf => f
  | Node i_opt sO sI =>
    match f with
    | Leaf => Leaf
    | Node None fO fI => collapse (sift sO fO) (sift sI fI)
    | Node (Some j) fO fI =>
      match i_opt with
      | Some i =>
        if i =? j
        then collapse (sift sO fO) (sift sI fI)
        else Node (Some j) (sift sO fO) (sift sI fI)
      | None => Node (Some j) (sift sO fO) (sift sI fI)
      end
    end
  end.

(* Create identity sieve of depth n. *)
Fixpoint identity_sieve (n : nat) (r : positive) :=
  match n with
  | O => Leaf
  | S m => Node (Some (mirror r)) (identity_sieve m r~0) (identity_sieve m r~1)
  end.

(***
Theorems
*)

Local Ltac fmap_ind f :=
  induction f as [|j_opt fO IHfO fI IHfI]; simpl; intros.

(* Equality is decidable. *)

Theorem fmap_eq_dec {V} :
  (∀v w : V, {v = w} + {v ≠ w}) ->
  ∀f g : fmap V, {f = g} + {f ≠ g}.
Proof.
intros V_dec f; induction f; destruct g; [left|right|right|]; try easy.
destruct (IHf1 g1); [subst|right; intros H; inv H].
destruct (IHf2 g2); [subst|right; intros H; inv H].
destruct val, val0; [|right|right|left]; try easy.
destruct (V_dec v v0); [left; subst; easy|right; intros H; inv H].
Qed.

Definition ffun_eq_dec := fmap_eq_dec Pos.eq_dec.

(* Theorems about lookup. *)

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
revert i; fmap_ind f.
apply lookup_create_eq.
destruct i; simpl; easy.
Qed.

Theorem lookup_insert_neq {V} f i j (v : V) :
  i ≠ j -> lookup (insert f i v) j = lookup f j.
Proof.
revert i j; fmap_ind f.
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

Theorem defined_dec {V} (f : fmap V) i :
  {Defined f i} + {¬Defined f i}.
Proof.
destruct (lookup f i); [left|right]; easy.
Qed.

Theorem defined_before_insert {V} f i j (v : V) :
  Defined f i -> Defined (insert f j v) i.
Proof.
rewrite lookup_insert; destruct (_ =? _); easy.
Qed.

Theorem lookup_mapval_none {V} t (f : fmap V) i :
  lookup f i = None -> lookup (mapval t f) i = None.
Proof.
revert i; fmap_ind f. easy.
destruct i, j_opt as [j|]; simpl; try easy.
all: try apply IHfO; try apply IHfI; easy.
Qed.

Theorem lookup_mapval_some {V} t f i (v : V) :
  lookup f i = Some v -> lookup (mapval t f) i = Some (t v).
Proof.
revert i; fmap_ind f. easy.
destruct j_opt as [j'|], i; simpl; try congruence.
all: try apply IHfO; try apply IHfI; easy.
Qed.

(* Theorems about size. *)

Theorem size_eq_length_values {V} (f : fmap V) :
  size f = length (values f).
Proof.
fmap_ind f. easy. destruct j_opt; simpl;
rewrite IHfO, IHfI, app_length; easy.
Qed.

(* Theorems about values. *)

Theorem in_values_create {V} i (v : V) :
  In v (values (create i v)).
Proof.
induction i; simpl; try rewrite app_nil_r; auto.
Qed.

Theorem in_values_insert {V} f i (v : V) :
  In v (values (insert f i v)).
Proof.
revert f; induction i; destruct f; simpl; auto.
1,3: try rewrite app_nil_r; apply in_values_create.
all: destruct val; try rewrite app_comm_cons; apply in_app_iff; auto.
left; apply in_cons, IHi.
Qed.

Theorem lookup_in_values {V} f i (v : V) :
  lookup f i = Some v -> In v (values f).
Proof.
revert i; fmap_ind f; [easy|intros]. destruct i, j_opt.
all: try rewrite app_comm_cons; apply in_app_iff.
1,2: right; eapply IHfI, H.
1,2: left; try apply in_cons; eapply IHfO, H.
left; inv H; apply in_eq. easy.
Qed.

Theorem apply_in_values f i :
  f⋅i ≠ i -> In f⋅i (values f).
Proof.
unfold apply; destruct (lookup f i) eqn:E; [|easy].
intros; eapply lookup_in_values, E.
Qed.

Theorem lookup_after_put f i j :
  lookup f i = Some i -> lookup (put j f) i = Some i.
Proof.
unfold put; rewrite lookup_insert.
destruct (_ =? _) eqn:E; convert_bool; subst; easy.
Qed.

Lemma lookup_fold_right_put range i f :
  In i range -> lookup (fold_right put f range) i = Some i.
Proof.
revert f; simple_ind range. destruct H; subst.
apply lookup_insert_eq. apply lookup_after_put, IHrange, H.
Qed.

Theorem lookup_union_range i f fs :
  In i (values f) -> In f fs -> lookup (union_range fs) i = Some i.
Proof.
intros; apply lookup_fold_right_put.
apply in_flat_map; exists f; easy.
Qed.

(* Theorems about apply and compose *)

Corollary apply_insert f i j :
  (insert f i j)⋅i = j.
Proof.
unfold apply; rewrite lookup_insert.
rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma lookup_compose_none gI g f i :
  lookup f i = None -> lookup (compose gI g f) i = lookup g i.
Proof.
revert g i; fmap_ind f. easy.
destruct j_opt as [j|], g, i; simpl; try easy.
1,2,5,6: apply lookup_mapval_none, H.
all: try rewrite IHfI; try rewrite IHfO; easy.
Qed.

Lemma lookup_compose_some gI g f i j :
  lookup f i = Some j -> lookup (compose gI g f) i = Some gI⋅j.
Proof.
revert g i; fmap_ind f. easy.
destruct j_opt as [j'|], g, i; simpl; try congruence.
all: try apply lookup_mapval_some; try apply IHfO; try apply IHfI; easy.
Qed.

Theorem apply_compose g f i :
  (g ∘ f)⋅i = g⋅(f⋅i).
Proof.
unfold apply; destruct (lookup f i) as [j|] eqn:H.
erewrite lookup_compose_some; easy.
erewrite lookup_compose_none; easy.
Qed.

Corollary compose_assoc f g h :
  (f ∘ g) ∘ h == f ∘ (g ∘ h).
Proof.
intros i; rewrite ?apply_compose; easy.
Qed.

Instance fmap_equivalence :
  Equivalence Equivalent.
Proof.
split; try easy. intros f g h Hf Hg i.
etransitivity; [apply Hf|apply Hg].
Qed.
