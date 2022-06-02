(* The Schreier-Sims subgroup chain algorithm. *)

From permlib Require Import perm.

Definition values {X} (m : Pmap X) : list X := (map_to_list m).*2.

Module Schreier.
Section Vector.

Definition vector := Pmap perm.

(* Add all numbers reachable from i. *)
Fixpoint extend (i : positive) (π : perm)
  (gen : list perm) (V : vector)
  (new : list positive) :=
  match gen with
  | [] => (V, new)
  | σ :: gen' =>
    let j := σ !!! i in
    match V !! j with
    | Some _ => extend i π gen' V new
    | None => extend i π gen' (<[j:=σ⋅π]> V) (j :: new)
    end
  end.

(* The generating set. *)
Variable gen : list perm.

(* Extend all numbers in the source list. *)
Fixpoint extend_loop (V : vector) (try new : list positive) :=
  match try with
  | [] => (V, new)
  | i :: try' =>
    match V !! i with
    | None => extend_loop V try' new
    | Some π =>
      match extend i π gen V new with
      | (V', new') => extend_loop V' try' new'
      end
    end
  end.

(* Repeat orbit extension n times. *)
Fixpoint loop (V : vector) (try : list positive) (n : nat) : vector :=
  match n with
  | O => V
  | S m =>
    match extend_loop V try [] with
    | (V', []) => V'
    | (V', new) => loop V' new m
    end
  end.

(* The stabilizer point. *)
Variable k : positive.

(* Build an orbit vector given an orbit size bound. *)
Definition build (bound : nat) : vector := loop (<[k:=∅]> ∅) [k] bound.

(* The orbit given by they keys of the Schreier vector. *)
Definition orbit (V : vector) : list positive := (map_to_list V).*1.

(* The subgroup generators according to Schreier's Lemma. *)
Definition generators (V : vector) : list perm :=
  let ϕ := inv <$> V in
  (λ σ_u, let σu := fst σ_u ⋅ snd σ_u in (default ∅ (ϕ !! (σu !!! k))) ⋅ σu) <$>
  (list_prod gen (values V)).

End Vector.
End Schreier.

Module Sims.
Section Filter.

Definition table := Pmap (Pmap perm).

(* Find the smallest mapping in π. *)
Definition minmap (π : perm) : option (positive * positive) :=
  let mappings := filter (λ m, fst m ≠ snd m) (map_to_list π) in
  match mappings with [] => None | m :: ms =>
    Some (foldl (λ m m', if decide (fst m < fst m') then m else m') m ms)
  end.

(* Add g to the table or discard it. *)
Fixpoint crack (T : table) (range : nat) (g : perm) : table :=
  match range with
  | O => T
  | S ran =>
    match minmap g with
    | None => T
    | Some (i, j) =>
      match T !! i with
      | None => <[i:={[j:=g]}]> T
      | Some Ti =>
        match Ti !! j with
        | None => <[i:=(<[j:=g]> Ti)]> T
        | Some h => crack T ran (inv g ⋅ h)
        end
      end
    end
  end.

Variable range : nat.

Fixpoint loop (gen : list perm) (T : table) : table :=
  match gen with
  | [] => T
  | g :: gen' => loop gen' (crack T range g)
  end.

Definition filter (gen : list perm) : list perm :=
  flat_map values (values (loop gen ∅)).

End Filter.
End Sims.

Module SGChain.

(* List of triples (gen, k, V) where orbit V = orbit of k in ⟨gen⟩). *)
Definition chain := list (list perm * positive * Schreier.vector).

Fixpoint loop range gen ks :=
  if (length gen =? 0)%nat then []
  else match ks with
  | [] => []
  | k :: ks' =>
    let V := Schreier.build gen k range in
    let gen' := Schreier.generators gen k V in
    let gen'' := Sims.filter range gen' in
    (gen, k, V) :: loop range gen'' ks'
  end.

Definition build gen ks :=
  let range := fold_left Pos.max ks 1 in
  let depth := Pos.size_nat range in
  loop (Pos.to_nat range) gen ks.

Definition order (C : chain) :=
  foldl Pos.mul 1 (Pos.of_nat ∘ size <$> C.*2).

End SGChain.
