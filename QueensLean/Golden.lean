import QueensLean.Ceiling

/-!
# The golden ceiling

Lean target 4 (2026-10-18) for "The fewest and the most toroidal conflicts". The closed form of `S(n)` is a concave
quadratic in `(A, G)` whose peak, at `A = αn/2` and `G = γn/2`, is exactly `n/φ`:
`S(n) = n/φ - (2√5/n) ((A - αn/2)² + (G - γn/2)²)` (`S_peak`). Hence `S(n) ≤ (√5 - 1) n/2` (`S_le`), and with
`Ceiling.conf_le_S` every `n`-queens solution has at most `(√5 - 1) n/2` toroidal conflicts, so at most `⌊n/φ⌋`
(`golden_ceiling`, the paper's Theorem `thm:golden`). This replaces the paper's integral and convexity step.
-/

open Finset Real

namespace Golden

open Queens FibSlack Ceiling

/-- The peak form of the closed form. -/
theorem S_peak {n A G : ℕ} (hn : 0 < n) (hA1 : (2 * (A : ℝ) - 1) ≤ α * n) (hA2 : α * n < 2 * (A : ℝ) + 1)
    (hG1 : (2 * (G : ℝ) - 1) ≤ γ * n) (hG2 : γ * n < 2 * (G : ℝ) + 1) :
    S n = (√5 - 1) / 2 * n - 2 * √5 / n * (((A : ℝ) - α * n / 2) ^ 2 + ((G : ℝ) - γ * n / 2) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [S_closed hn hA1 hA2 hG1 hG2, α_eq, γ_eq]
  have e : 3 * (A : ℝ) + G + √5 * (G - A - 2 * ((A : ℝ) ^ 2 + (G : ℝ) ^ 2) / n) -
      ((√5 - 1) / 2 * n - 2 * √5 / n * (((A : ℝ) - (3 * √5 - 5) / 10 * n / 2) ^ 2 +
        ((G : ℝ) - (√5 + 5) / 10 * n / 2) ^ 2)) =
      (-12 * (A : ℝ) - 4 * G + n * √5 - 2 * n) / 20 * (√5 ^ 2 - 5) := by
    field_simp; ring
  rw [s5_sq, sub_self, mul_zero] at e
  linarith

/-- `S(n) ≤ (√5 - 1) n/2` for every `n ≥ 1`. -/
theorem S_le {n : ℕ} (hn : 0 < n) : S n ≤ (√5 - 1) / 2 * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hα0 : 0 ≤ α := by rw [α_eq]; linarith [s5_gt]
  have hγ0 : 0 ≤ γ := by rw [γ_eq]; positivity
  set A := ⌊(α * n + 1) / 2⌋₊
  set G := ⌊(γ * n + 1) / 2⌋₊
  have a1 := Nat.floor_le (show 0 ≤ (α * n + 1) / 2 by positivity)
  have a2 := Nat.lt_floor_add_one ((α * n + 1) / 2)
  have g1 := Nat.floor_le (show 0 ≤ (γ * n + 1) / 2 by positivity)
  have g2 := Nat.lt_floor_add_one ((γ * n + 1) / 2)
  rw [S_peak (A := A) (G := G) hn (by linarith) (by linarith) (by linarith) (by linarith)]
  have : 0 ≤ 2 * √5 / n * (((A : ℝ) - α * n / 2) ^ 2 + ((G : ℝ) - γ * n / 2) ^ 2) := by positivity
  linarith

/-- `n/φ = (√5 - 1) n/2`. -/
theorem div_gold (n : ℝ) : n / goldenRatio = (√5 - 1) / 2 * n := by
  rw [div_eq_mul_inv, inv_goldenRatio, goldenConj]; ring

/-- **Golden ceiling**: every `n`-queens solution has at most `(√5 - 1) n/2` toroidal conflicts, so at most
`⌊n/φ⌋`. -/
theorem golden_ceiling {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (hs : Function.Injective (vs p))
    (hd : Function.Injective (vd p)) :
    (conf p : ℝ) ≤ (√5 - 1) / 2 * n ∧ (conf p : ℤ) ≤ ⌊(n : ℝ) / goldenRatio⌋ := by
  have h := (conf_le_S p hs hd).trans (S_le (Nat.pos_of_ne_zero (NeZero.ne n)))
  refine ⟨h, ?_⟩
  rw [Int.le_floor, div_gold]
  exact_mod_cast h

end Golden

#print axioms Golden.S_le
#print axioms Golden.golden_ceiling
