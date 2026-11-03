import QueensLean.FloorAll
import QueensLean.Levels
import QueensLean.Golden
import SecondLean.Paths

/-!
# Specification: the paper's notions defined from the board, naively

The proofs use compact definitions (`Equiv.Perm`, injectivity of `vs`/`vd`, classes in `ZMod n`). A reader checking
that the Lean theorems say what the papers say should not have to trust those. This file defines everything again in
the plainest chess terms, proves the plain definitions equal the compact ones, and restates the main results in plain
terms. To trust the results, read only the definitions in Part 1 and the statements in Part 3.

* A board is a function `f : Fin n → Fin n`: row `i` holds a queen in column `f i`.
* Solution (`IsSolution`): no two queens share a column, and no two share a diagonal: `|r - r'| ≠ |c - c'|`.
* Wrapped sum diagonal of a square: `(r + c) mod n`; wrapped difference diagonal: `(r + n - c) mod n`.
* Conflicts (`confSpec`): pairs of queens `i < j` on a common wrapped sum diagonal, plus pairs on a common wrapped
  difference diagonal (Engelhardt's count, both families counted separately).
* Conflict graph (`graphSpec`): queens joined when they share a wrapped diagonal.
-/

open Finset Real

namespace SecondLean.Spec

variable {n : ℕ}

/-! ## Part 1: plain definitions -/

/-- A solution: no two queens in one column and no two on one diagonal. -/
def IsSolution (f : Fin n → Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ j → f i ≠ f j ∧ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≠ |((f i : ℕ) : ℤ) - ((f j : ℕ) : ℤ)|

instance (f : Fin n → Fin n) : Decidable (IsSolution f) := by unfold IsSolution; infer_instance

/-- Wrapped sum diagonal of the queen in row `i`. -/
def sumDiag (f : Fin n → Fin n) (i : Fin n) : ℕ := ((i : ℕ) + (f i : ℕ)) % n

/-- Wrapped difference diagonal of the queen in row `i`. -/
def difDiag (f : Fin n → Fin n) (i : Fin n) : ℕ := ((i : ℕ) + n - (f i : ℕ)) % n

/-- Conflicts: pairs of rows `i < j` on a common wrapped sum diagonal plus pairs on a common wrapped difference
diagonal. -/
def confSpec (f : Fin n → Fin n) : ℕ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ sumDiag f q.1 = sumDiag f q.2)).card +
    ((univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ difDiag f q.1 = difDiag f q.2)).card

/-- The conflict graph: two queens are joined when they share a wrapped diagonal. -/
def graphSpec (f : Fin n → Fin n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (sumDiag f i = sumDiag f j ∨ difDiag f i = difDiag f j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp Eq.symm Eq.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-! ## Part 2: the plain definitions equal the compact ones -/

theorem isSolution_iff (p : Equiv.Perm (Fin n)) :
    IsSolution p ↔ Function.Injective (Ceiling.vs p) ∧ Function.Injective (Ceiling.vd p) := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · by_contra hne
      apply (h i j hne).2
      rw [abs_eq_abs]; right
      simp only [Ceiling.vs] at hij; omega
    · by_contra hne
      apply (h i j hne).2
      rw [abs_eq_abs]; left
      simp only [Ceiling.vd] at hij; omega
  · rintro ⟨hs, hd⟩ i j hij
    refine ⟨fun e => hij (p.injective e), fun habs => ?_⟩
    rcases abs_eq_abs.mp habs with e | e
    · exact hij (hd (by simp only [Ceiling.vd]; omega))
    · exact hij (hs (by simp only [Ceiling.vs]; omega))

section NZ

theorem sumDiag_eq_iff (p : Equiv.Perm (Fin n)) (i j : Fin n) :
    sumDiag p i = sumDiag p j ↔ Queens.sumCls p i = Queens.sumCls p j := by
  unfold sumDiag Queens.sumCls
  rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']

theorem difCls_eq_cast (p : Equiv.Perm (Fin n)) (i : Fin n) :
    Queens.difCls p i = (((i : ℕ) + n - (p i : ℕ) : ℕ) : ZMod n) := by
  have hle : (p i : ℕ) ≤ (i : ℕ) + n := by have := (p i).isLt; omega
  unfold Queens.difCls
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem difDiag_eq_iff (p : Equiv.Perm (Fin n)) (i j : Fin n) :
    difDiag p i = difDiag p j ↔ Queens.difCls p i = Queens.difCls p j := by
  unfold difDiag
  rw [difCls_eq_cast, difCls_eq_cast, ZMod.natCast_eq_natCast_iff']

theorem confSpec_eq (p : Equiv.Perm (Fin n)) : confSpec p = Queens.conf p := by
  unfold confSpec Queens.conf Queens.pairs
  congr 1
  · congr 1; apply Finset.filter_congr; intro q _; rw [sumDiag_eq_iff]
  · congr 1; apply Finset.filter_congr; intro q _; rw [difDiag_eq_iff]

theorem graphSpec_eq (p : Equiv.Perm (Fin n)) : graphSpec p = NoCycles.conflictGraph p := by
  ext i j
  simp only [graphSpec, NoCycles.conflictGraph, sumDiag_eq_iff, difDiag_eq_iff]

end NZ

/-- A solution as a permutation (its columns are distinct, so it is a bijection of `Fin n`). -/
noncomputable def toPerm (f : Fin n → Fin n) (h : IsSolution f) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.mp
    (fun i j e => by by_contra hne; exact (h i j hne).1 e))

theorem toPerm_coe (f : Fin n → Fin n) (h : IsSolution f) : ⇑(toPerm f h) = f := rfl

/-! ## Part 3: the main results in plain terms -/

section NZ3
variable [NeZero n]

omit [NeZero n] in
theorem solution_hyps (f : Fin n → Fin n) (h : IsSolution f) :
    Function.Injective (Ceiling.vs (toPerm f h)) ∧ Function.Injective (Ceiling.vd (toPerm f h)) :=
  (isSolution_iff (toPerm f h)).mp h

/-- **Paper 1, Theorem 2 (floor).** For `n ≠ 2, 3` the least number of conflicts of a solution is `f(n)`. -/
theorem floor (h2 : n ≠ 2) (h3 : n ≠ 3) :
    (∃ f : Fin n → Fin n, IsSolution f ∧ confSpec f = Layer.floorVal n) ∧
      ∀ f : Fin n → Fin n, IsSolution f → Layer.floorVal n ≤ confSpec f := by
  obtain ⟨⟨p, hs, hd, hc⟩, hall⟩ := Construct.floor_exact n h2 h3
  refine ⟨⟨p, (isSolution_iff p).mpr ⟨hs, hd⟩, by rw [confSpec_eq]; exact hc⟩, fun f hf => ?_⟩
  have := hall (toPerm f hf)
  rwa [← confSpec_eq, toPerm_coe] at this

/-- **Paper 1, Theorem 3 (forbidden levels).** -/
theorem levels (f : Fin n → Fin n) (hf : IsSolution f) :
    confSpec f ≠ 1 ∧ (n.Prime → 5 ≤ n → confSpec f ≠ 2) ∧
      ∀ q : ℕ, q.Prime → 5 ≤ q → n = 2 * q → confSpec f ≠ 3 := by
  have := Levels.levels (toPerm f hf)
  rwa [← confSpec_eq, toPerm_coe] at this

omit [NeZero n] in
/-- **Paper 1, Theorem 5 (no cycles, union of paths).** -/
theorem union_of_paths (f : Fin n → Fin n) (hf : IsSolution f) :
    (graphSpec f).IsAcyclic ∧ ∀ i, ((graphSpec f).neighborSet i).ncard ≤ 2 := by
  obtain ⟨hs, hd⟩ := solution_hyps f hf
  have := Paths.union_of_paths hs hd
  rwa [← graphSpec_eq, toPerm_coe] at this

/-- **Paper 1, Theorem 17 (golden ceiling).** -/
theorem golden_ceiling (f : Fin n → Fin n) (hf : IsSolution f) :
    (confSpec f : ℝ) ≤ (√5 - 1) / 2 * n := by
  obtain ⟨hs, hd⟩ := solution_hyps f hf
  have := (Golden.golden_ceiling (toPerm f hf) hs hd).1
  rwa [← confSpec_eq, toPerm_coe] at this

end NZ3

/-! ## Part 4: sanity checks on explicit boards (the plain definitions compute the expected numbers) -/

/-- The two solutions at `n = 4` have 2 conflicts each (Engelhardt's table, A181499). -/
example : IsSolution (![1, 3, 0, 2] : Fin 4 → Fin 4) ∧ confSpec (![1, 3, 0, 2] : Fin 4 → Fin 4) = 2 := by decide

/-- A solution at `n = 6`: 3 conflicts, the floor `f(6) = 3`. -/
example : IsSolution (![1, 3, 5, 0, 2, 4] : Fin 6 → Fin 6) ∧ confSpec (![1, 3, 5, 0, 2, 4] : Fin 6 → Fin 6) = 3 := by
  decide

/-- Pólya's toroidal solution at `n = 5`: no conflicts. -/
example : IsSolution (![0, 2, 4, 1, 3] : Fin 5 → Fin 5) ∧ confSpec (![0, 2, 4, 1, 3] : Fin 5 → Fin 5) = 0 := by decide

/-- Paper 1's example after Corollary 19: a solution at `n = 26` with `C(26) = 16` conflicts. -/
example : IsSolution (![16, 11, 19, 7, 4, 17, 21, 2, 5, 22, 1, 25, 13, 15, 0, 24, 10, 23, 6, 18, 3, 8, 20, 12, 14, 9] :
      Fin 26 → Fin 26) ∧
    confSpec (![16, 11, 19, 7, 4, 17, 21, 2, 5, 22, 1, 25, 13, 15, 0, 24, 10, 23, 6, 18, 3, 8, 20, 12, 14, 9] :
      Fin 26 → Fin 26) = 16 := by decide +kernel

/-- Controls: the main diagonal is not a solution; a board with a shared column is not a solution. -/
example : ¬ IsSolution (![0, 1, 2, 3] : Fin 4 → Fin 4) := by decide
example : ¬ IsSolution (![1, 3, 0, 1] : Fin 4 → Fin 4) := by decide

end SecondLean.Spec

#print axioms SecondLean.Spec.confSpec_eq
#print axioms SecondLean.Spec.graphSpec_eq
#print axioms SecondLean.Spec.isSolution_iff
#print axioms SecondLean.Spec.floor
#print axioms SecondLean.Spec.levels
#print axioms SecondLean.Spec.union_of_paths
#print axioms SecondLean.Spec.golden_ceiling
#print axioms SecondLean.Spec.sumDiag_eq_iff
#print axioms SecondLean.Spec.difCls_eq_cast
#print axioms SecondLean.Spec.difDiag_eq_iff
#print axioms SecondLean.Spec.toPerm_coe
#print axioms SecondLean.Spec.solution_hyps
