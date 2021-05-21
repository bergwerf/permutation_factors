(* The Schreier-Sims algorithm to factor a group into a chain of subgroups. *)

From CGT Require Import A1_setup B1_fmap B2_perm.
From CGT Require Import C1_Schreier_vector C2_Sims_filter.

(* Factor a group into a sub-group chain. *)
Module SGChain.

(* List of triples (gen, k, V) where orbit V = orbit of k in ⟨gen⟩). *)
Definition chain := list (list perm × positive × Schreier.vector).

Fixpoint loop sieve range gen ks :=
  if (length gen =? 0)%nat then []
  else match ks with
  | [] => []
  | k :: ks' =>
    let V := Schreier.build gen k (length ks) in
    let gen' := Schreier.generators gen k V in
    let gen'' := Sims.filter sieve range gen' in
    (gen, k, V) :: loop sieve range gen'' ks'
  end.

Definition build gen ks :=
  let range := fold_left Pos.max ks 1 in
  let depth := Pos.size_nat range in
  let sieve := identity_sieve depth xH in
  loop sieve (Pos.to_nat range) gen ks.

End SGChain.
