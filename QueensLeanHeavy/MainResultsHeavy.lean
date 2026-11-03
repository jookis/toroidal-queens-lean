import QueensLeanHeavy.MissC10
import QueensLeanHeavy.MissC13

/-!
# Main results, heavy part: the two sizes below the ceiling

Corollary 19 at `n = 10` and `n = 13`: the ceiling is one less than `⌊n/φ⌋`. Both rest on an exhaustive search
evaluated in the kernel (`decide +kernel`); see `MissC10.lean` and `MissC13.lean`. Restated here with the definitions
of `QueensLean/MainResults.lean`; the proofs are the module theorems.
-/

namespace MainResults

/-- **Corollary 19 at 10.** `C(10) = 5 = ⌊10/φ⌋ - 1`. -/
theorem C_10 : ⌊(10 : ℝ) / Real.goldenRatio⌋ = 6 ∧
    (∃ p : Equiv.Perm (Fin 10), Function.Injective (Ceiling.vs p) ∧ Function.Injective (Ceiling.vd p) ∧
      Queens.conf p = 5) ∧
    ∀ p : Equiv.Perm (Fin 10), Function.Injective (Ceiling.vs p) → Function.Injective (Ceiling.vd p) →
      Queens.conf p ≤ 5 :=
  Misses.C_10

/-- **Corollary 19 at 13.** `C(13) = 7 = ⌊13/φ⌋ - 1`. -/
theorem C_13 : ⌊(13 : ℝ) / Real.goldenRatio⌋ = 8 ∧
    (∃ p : Equiv.Perm (Fin 13), Function.Injective (Ceiling.vs p) ∧ Function.Injective (Ceiling.vd p) ∧
      Queens.conf p = 7) ∧
    ∀ p : Equiv.Perm (Fin 13), Function.Injective (Ceiling.vs p) → Function.Injective (Ceiling.vd p) →
      Queens.conf p ≤ 7 :=
  Misses.C_13

end MainResults
