(* The Schreier-Sims subgroup chain algorithm. *)

From stdpp Require Import pmap gmap.
From permlib Require Import perm.

(* This has nicer unfolding behavior than Nat.iter. *)
Fixpoint iterate {X} (n : nat) (f : X -> X) (x : X) :=
  match n with O => x | S m => iterate m f (f x) end.

Module Schreier.
Section Vector.

Definition orbit : Type := Pmap perm.
Definition state : Type := orbit * list (positive * perm).

(* Given i = π !!! k, add j = σ !!! i to the orbit vector using σ⋅π. *)
Definition extend (i : positive) (π : perm) (s : state) (σ : perm) : state :=
  let (orb, cur) := s in let j := σ !!! i in if orb !! j then (orb, cur) else
  let τ := σ⋅π in (<[j:=τ]> orb, (j, τ) :: cur).

(* Extend the orbit from previously discovered indices. *)
Definition build_step gen (s : state) :=
  foldl (λ s p, foldl (extend p.1 p.2) s gen) (s.1, []) s.2.

(* Build the orbit of k using size bound n. *)
Definition build gen k n : state :=
  iterate n (build_step gen) ({[k:=∅]}, [(k, ∅)]).

(* The subgroup generators according to Schreier's Lemma. *)
Definition generators gen k (orb : orbit) : list perm :=
  let ϕ := inv <$> orb in (λ σ_u,
  let σu := σ_u.1 ⋅ σ_u.2 in
  let inv_σu := default ∅ (ϕ !! (σu !!! k)) in
  inv_σu ⋅ σu) <$> list_prod gen (values orb).

End Vector.
End Schreier.

Module Sims.
Section Filter.

Definition table := gmap (positive * positive) perm.

(* Find the smallest mapping in π. *)
Definition minmap (π : perm) : option (positive * positive) :=
  let mappings := filter (λ p, p.1 ≠ p.2) (map_to_list π) in
  match mappings with [] => None | p :: ps =>
  Some (foldl (λ p q, if decide (p.1 < q.1) then p else q) p ps)
  end.

(* Add π to the table or discard it. *)
Fixpoint crack (n : nat) (tb : table) (π : perm) : table :=
  match n with O => tb | S m =>
  match minmap π with None => tb | Some p =>
  match tb !! p with
  | None => <[p:=π]> tb
  | Some τ => crack m tb (inv π ⋅ τ)
  end end end.

(* Filter a generating set using at most n crack cycles. *)
Definition filter n gen : table :=
  foldl (crack n) ∅ gen.

End Filter.
End Sims.

Module SGChain.

(* (generating set, stabilizer point k, orbit of k in ⟨gen⟩). *)
Definition chain := list (list perm * positive * Schreier.orbit).

Definition stabilize range (s : chain * list perm) k : chain * list perm :=
  let (ch, gen) := s in
  if decide (gen = []) then ([], []) else
  let orb  := Schreier.build gen k (Pos.to_nat range) in
  let gen1 := Schreier.generators gen k orb.1 in
  let gen2 := values (Sims.filter (Pos.to_nat range) gen1) in
  (ch ++ [(gen, k, orb.1)], gen2).

Definition build gen ks : chain :=
  let range := fold_left Pos.max ks 1 in
  let depth := Pos.size_nat range in
  (foldl (stabilize range) ([], gen) ks).1.

Definition order (ch : chain) :=
  foldl Pos.mul 1 (Pos.of_nat ∘ size <$> ch.*2).

End SGChain.
