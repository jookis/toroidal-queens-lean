import QueensLean.Misses

/-! `C(10) = 5 = ⌊10/φ⌋ - 1` by exhaustive search in the kernel (`Misses.go`, `decide +kernel`). -/

namespace Misses

open Queens Ceiling Boards

/-- **`C(10) = 5`**, one below `⌊10/φ⌋ = 6`. -/
theorem C_10 : ⌊(10 : ℝ) / Real.goldenRatio⌋ = 6 ∧
    (∃ p : Equiv.Perm (Fin 10), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧ conf p = 5) ∧
    ∀ p : Equiv.Perm (Fin 10), Function.Injective (vs p) → Function.Injective (vd p) → conf p ≤ 5 :=
  ⟨floor_eq_of (by norm_num) (by norm_num), sound (L := [1, 5, 2, 6, 9, 0, 8, 4, 7, 3]) (by decide +kernel),
    fun p hs hd => go_sound (k := 5) (by decide +kernel) p hs hd⟩

end Misses

#print axioms Misses.C_10
