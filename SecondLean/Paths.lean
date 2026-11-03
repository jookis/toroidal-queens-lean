import QueensLean.NoCycles

/-!
# The conflict graph of a solution is a union of paths

Paper 1, Theorem 5 says the conflict graph of an `n`-queens solution "has no cycle; it is a union of paths". The v4
Lean package proves the first part (`NoCycles.acyclic`). This file adds the second: every queen has at most two
neighbours (at most one sum partner and one difference partner, `NoCycles.SP_unique`, `NoCycles.DP_unique`). A graph
with no cycle and all degrees at most two is a disjoint union of paths; `union_of_paths` states exactly that pair.
-/

namespace SecondLean.Paths

open Queens Ceiling NoCycles

variable {n : ℕ} {p : Equiv.Perm (Fin n)}

/-- Every queen of a solution has at most two neighbours in the conflict graph. -/
theorem degree_le_two (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) (i : Fin n) :
    ((conflictGraph p).neighborSet i).ncard ≤ 2 := by
  have hsub : (conflictGraph p).neighborSet i ⊆ {j | SP p i j} ∪ {j | DP p i j} := by
    intro j hj
    obtain ⟨hij, h⟩ := hj
    rcases h with h | h
    · exact Or.inl ⟨fun e => hij e.symm, h.symm⟩
    · exact Or.inr ⟨fun e => hij e.symm, h.symm⟩
  have h1 : {j | SP p i j}.ncard ≤ 1 :=
    Set.ncard_le_one_iff_subsingleton.mpr (fun a ha b hb => SP_unique hs ha hb)
  have h2 : {j | DP p i j}.ncard ≤ 1 :=
    Set.ncard_le_one_iff_subsingleton.mpr (fun a ha b hb => DP_unique hd ha hb)
  calc ((conflictGraph p).neighborSet i).ncard
      ≤ ({j | SP p i j} ∪ {j | DP p i j}).ncard := Set.ncard_le_ncard hsub
    _ ≤ {j | SP p i j}.ncard + {j | DP p i j}.ncard := Set.ncard_union_le _ _
    _ ≤ 2 := by omega

/-- **Theorem 5, full form.** The conflict graph of a solution has no cycle and every degree is at most two, so it is
a disjoint union of paths. -/
theorem union_of_paths (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) :
    (conflictGraph p).IsAcyclic ∧ ∀ i, ((conflictGraph p).neighborSet i).ncard ≤ 2 :=
  ⟨acyclic hs hd, degree_le_two hs hd⟩

end SecondLean.Paths

#print axioms SecondLean.Paths.degree_le_two
#print axioms SecondLean.Paths.union_of_paths
