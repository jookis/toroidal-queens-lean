import Mathlib

/-!
# The Fibonacci slack theorem

Lean target 2 (2026-10-18) for "The fewest and the most toroidal conflicts". With `ℓ = √5`,
`α = (3 - ℓ)/(2ℓ)`, `γ = (1 + ℓ)/(2ℓ)`, the paper's convex function `g` on `[0, 1]`, the row distances
`ρ_r = (n - |2r - (n - 1)|)/n` and `S(n) = 2 ∑_r g(ρ_r)` (the bound in the proof of the golden ceiling), this file
proves for `n = F_m`:

* `S_closed`: `S(n) = 3A + G + ℓ (G - A - 2(A² + G²)/n)` for `n ≥ 1`, where `A` and `G` count the odd numbers
  `k` with `k ≤ αn` and `k ≤ γn`;
* `slack_zero`: `S(F_m) = ⌊F_m/φ⌋` for `m ≥ 5`, `m ≡ 1, 3 (mod 6)`;
* `slack_neg`: `⌊F_m/φ⌋ - 1 < S(F_m) < ⌊F_m/φ⌋` for `m ≥ 5`, `m ≡ 5 (mod 6)`;
* `slack_even`: `⌊F_m/φ⌋ < S(F_m) < ⌊F_m/φ⌋ + 1` for even `m ≥ 6`.

The discrete bound `C(n) ≤ ⌊S(n)⌋` itself (the paper's loss argument) is not formalized here.
-/

open Finset Real

namespace FibSlack

noncomputable section

/-- `α = (3 - √5)/(2√5)`. -/
def α : ℝ := (3 - √5) / (2 * √5)

/-- `γ = (1 + √5)/(2√5)`. -/
def γ : ℝ := (1 + √5) / (2 * √5)

/-- The paper's convex function `g` (the pieces agree at `α` and `γ`). -/
def g (x : ℝ) : ℝ := if x ≤ α then 1 - √5 * x else if x ≤ γ then √5 / 2 * (γ - x) else 0

/-- Distance of row `r` from the nearer edge, on a scale where the middle row is `1`. -/
def ρ (n r : ℕ) : ℝ := ((n : ℝ) - |2 * (r : ℝ) - ((n : ℝ) - 1)|) / n

/-- The bound `S(n) = 2 ∑_r g(ρ_r)`. -/
def S (n : ℕ) : ℝ := 2 * ∑ r ∈ range n, g (ρ n r)

theorem s5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem s5_gt : (2 : ℝ) < √5 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem s5_lt : (√5 : ℝ) < 9 / 4 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem α_eq : α = (3 * √5 - 5) / 10 := by
  have h := s5_gt
  unfold α
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination (-6 : ℝ) * s5_sq

theorem γ_eq : γ = (√5 + 5) / 10 := by
  have h := s5_gt
  unfold γ
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination (-2 : ℝ) * s5_sq

theorem α_lt_γ : α < γ := by
  rw [α_eq, γ_eq]; linarith [s5_lt]

/-- For `r < n`, `ρ_r = (2 min(r, n - 1 - r) + 1)/n`. -/
theorem ρ_eq (n r : ℕ) (hr : r < n) :
    ρ n r = (2 * ((min r (n - 1 - r) : ℕ) : ℝ) + 1) / n := by
  unfold ρ
  congr 1
  rcases le_total r (n - 1 - r) with h | h
  · rw [min_eq_left h]
    have h1 : 2 * r + 1 ≤ n := by omega
    have h2 : (2 * (r : ℝ) + 1) ≤ n := by exact_mod_cast h1
    rw [abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h]
    have h1 : n ≤ 2 * r + 1 := by omega
    have h2 : (n : ℝ) ≤ 2 * r + 1 := by exact_mod_cast h1
    have hc : ((n - 1 - r : ℕ) : ℝ) = n - 1 - r := by
      rw [Nat.cast_sub (show r ≤ n - 1 by omega), Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    rw [hc, abs_of_nonneg (by linarith)]; ring

/-- `g` at the odd point `(2j + 1)/n`. -/
def H (n j : ℕ) : ℝ := g ((2 * (j : ℝ) + 1) / n)

/-- `∑_{r<k} (u + v(2r + 1)) = k u + v k²`. -/
theorem lin_sum (u v : ℝ) (k : ℕ) :
    ∑ r ∈ range k, (u + v * (2 * (r : ℝ) + 1)) = k * u + v * (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

section closed

variable {n A G : ℕ}

theorem H_first (hn : 0 < n) (hA : (2 * (A : ℝ) - 1) ≤ α * n) {j : ℕ} (hj : j < A) :
    H n j = 1 + (-(√5) / n) * (2 * (j : ℝ) + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj' : (j : ℝ) + 1 ≤ A := by exact_mod_cast hj
  have hx : (2 * (j : ℝ) + 1) / n ≤ α := by
    rw [div_le_iff₀ hn']; linarith
  unfold H g
  simp only [hx, ↓reduceIte]; ring

theorem H_mid (hn : 0 < n) (hA : α * n < 2 * (A : ℝ) + 1) (hG : (2 * (G : ℝ) - 1) ≤ γ * n) {j : ℕ}
    (hj1 : A ≤ j) (hj2 : j < G) :
    H n j = √5 * γ / 2 + (-(√5) / (2 * n)) * (2 * (j : ℝ) + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj1' : (A : ℝ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℝ) + 1 ≤ G := by exact_mod_cast hj2
  have hx1 : ¬ (2 * (j : ℝ) + 1) / n ≤ α := by
    rw [not_le, lt_div_iff₀ hn']; linarith
  have hx2 : (2 * (j : ℝ) + 1) / n ≤ γ := by
    rw [div_le_iff₀ hn']; linarith
  unfold H g
  simp only [hx1, hx2, ↓reduceIte]
  field_simp
  ring

theorem H_zero (hn : 0 < n) (hG : γ * n < 2 * (G : ℝ) + 1) {j : ℕ} (hj : G ≤ j) : H n j = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hj' : (G : ℝ) ≤ j := by exact_mod_cast hj
  have hx2 : ¬ (2 * (j : ℝ) + 1) / n ≤ γ := by
    rw [not_le, lt_div_iff₀ hn']; linarith
  have hx1 : ¬ (2 * (j : ℝ) + 1) / n ≤ α := fun h => hx2 (h.trans α_lt_γ.le)
  unfold H g
  simp only [hx1, hx2, ↓reduceIte]

/-- **Closed form** of `S(n)` for `n ≥ 1`. -/
theorem S_closed (hn : 0 < n) (hA1 : (2 * (A : ℝ) - 1) ≤ α * n) (hA2 : α * n < 2 * (A : ℝ) + 1)
    (hG1 : (2 * (G : ℝ) - 1) ≤ γ * n) (hG2 : γ * n < 2 * (G : ℝ) + 1) :
    S n = 3 * A + G + √5 * (G - A - 2 * ((A : ℝ) ^ 2 + (G : ℝ) ^ 2) / n) := by
  have hn0 : 0 < n := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : γ < 1 := by rw [γ_eq]; linarith [s5_lt]
  have hαγ := α_lt_γ
  -- `2G ≤ n` (from `2G - 1 ≤ γ n < n`) and `A ≤ G`
  have h2G : 2 * G ≤ n := by
    have : (2 * (G : ℝ)) < n + 1 := by nlinarith
    have : 2 * G < n + 1 := by exact_mod_cast this
    omega
  have hAG : A ≤ G := by
    have : (A : ℝ) < G + 1 := by nlinarith
    have : A < G + 1 := by exact_mod_cast this
    omega
  -- fold the two halves of the board
  have hpt : ∀ r ∈ range n, g (ρ n r) = H n r + H n (n - 1 - r) := by
    intro r hr
    rw [mem_range] at hr
    rw [ρ_eq n r hr]
    change H n (min r (n - 1 - r)) = _
    by_cases h1 : r < G
    · rw [show min r (n - 1 - r) = r by omega, H_zero hn0 hG2 (show G ≤ n - 1 - r by omega), add_zero]
    · rw [H_zero hn0 hG2 (show G ≤ r by omega), zero_add]
      by_cases h2 : n - 1 - r < G
      · rw [show min r (n - 1 - r) = n - 1 - r by omega]
      · rw [H_zero hn0 hG2 (show G ≤ min r (n - 1 - r) by omega),
          H_zero hn0 hG2 (show G ≤ n - 1 - r by omega)]
  have hsum : ∑ r ∈ range n, g (ρ n r) = 2 * ∑ r ∈ range n, H n r := by
    rw [sum_congr rfl hpt, sum_add_distrib, sum_range_reflect (fun j => H n j) n]; ring
  -- cut the sum at `G`, then at `A`
  have hcutG : ∑ r ∈ range n, H n r = ∑ r ∈ range G, H n r := by
    rw [← sum_range_add_sum_Ico _ (show G ≤ n by omega)]
    rw [sum_eq_zero (fun j hj => H_zero hn0 hG2 (mem_Ico.mp hj).1), add_zero]
  have hcutA : ∑ r ∈ range G, H n r = ∑ r ∈ range A, H n r + ∑ r ∈ Ico A G, H n r :=
    (sum_range_add_sum_Ico _ hAG).symm
  have hfirst : ∑ r ∈ range A, H n r = A * 1 + (-(√5) / n) * (A : ℝ) ^ 2 := by
    rw [sum_congr rfl (fun j hj => H_first hn0 hA1 (mem_range.mp hj)), lin_sum]
  have hmid : ∑ r ∈ Ico A G, H n r =
      (G * (√5 * γ / 2) + (-(√5) / (2 * n)) * (G : ℝ) ^ 2) -
      (A * (√5 * γ / 2) + (-(√5) / (2 * n)) * (A : ℝ) ^ 2) := by
    rw [sum_congr rfl (fun j hj => H_mid hn0 hA2 hG1 (mem_Ico.mp hj).1 (mem_Ico.mp hj).2),
      sum_Ico_eq_sub _ hAG, lin_sum, lin_sum]
  unfold S
  rw [hsum, hcutG, hcutA, hfirst, hmid, γ_eq]
  linear_combination ((G : ℝ) - A) / 5 * s5_sq

end closed

/-! ### Fibonacci part -/

/-- `X m = 3 L_m - 5 F_m + 10` and `Y m = 5 F_m + L_m + 10`, with `L_m = 2 F_{m+1} - F_m`. -/
def X (m : ℕ) : ℤ := 6 * (Nat.fib (m + 1) : ℤ) - 8 * Nat.fib m + 10
def Y (m : ℕ) : ℤ := 2 * (Nat.fib (m + 1) : ℤ) + 4 * Nat.fib m + 10

theorem XY_period (k : ℕ) : X (k + 12) % 20 = X k % 20 ∧ Y (k + 12) % 20 = Y k % 20 := by
  have h12 : Nat.fib (k + 12) = Nat.fib k * 89 + Nat.fib (k + 1) * 144 := by
    rw [show k + 12 = k + 11 + 1 by rfl, Nat.fib_add]; norm_num
  have h13 : Nat.fib (k + 13) = Nat.fib k * 144 + Nat.fib (k + 1) * 233 := by
    rw [show k + 13 = k + 12 + 1 by rfl, Nat.fib_add]; norm_num
  unfold X Y
  rw [show k + 12 + 1 = k + 13 by rfl, h12, h13]
  push_cast
  constructor <;> omega

theorem XY_mod (m : ℕ) : X m % 20 = X (m % 12) % 20 ∧ Y m % 20 = Y (m % 12) % 20 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 12
    · rw [Nat.mod_eq_of_lt hm]; exact ⟨rfl, rfl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 12 := ⟨m - 12, by omega⟩
      obtain ⟨h1, h2⟩ := ih k (by omega)
      obtain ⟨p1, p2⟩ := XY_period k
      rw [show (k + 12) % 12 = k % 12 by omega]
      exact ⟨p1.trans h1, p2.trans h2⟩

/-- The algebraic core: one identity for all classes (cofactors from sympy). -/
theorem core (s F t e L A G c a b d : ℝ) (hs : s ^ 2 = 5) (hL : L = s * F + 2 * t)
    (he : t ^ 2 + s * F * t = e) (hA : 20 * A = 3 * L - 5 * F + 10 - a)
    (hG : 20 * G = 5 * F + L + 10 - b) (hc : 2 * c = L - F - 2 * d) :
    F * (3 * A + G - c) + s * (F * (G - A) - 2 * (A ^ 2 + G ^ 2)) =
      F * d + s * (-a ^ 2 / 200 + a / 10 - b ^ 2 / 200 + b / 10 - e / 5 - 1) +
        s * t * (3 * a + b - 40) / 50 := by
  linear_combination ((-20 * A * s - 5 * F * s + 30 * F - 3 * L * s + a * s - 10 * s) / 200) * hA +
    ((5 * F * s + 10 * F - 20 * G * s - L * s + b * s - 10 * s) / 200) * hG + (-F / 2) * hc +
    (-s * (5 * F * s + 5 * L - 3 * a - b + 10 * t + 40) / 100) * hL + (-s / 5) * he +
    (-F * (5 * F * s - 3 * a - b + 40) / 100) * hs

/-- `|ψ^m| < 1/10` for `m ≥ 5`. -/
theorem t_small {m : ℕ} (hm : 5 ≤ m) : |goldenConj ^ m| < 1 / 10 := by
  have h1 : |goldenConj| < 31 / 50 := by
    rw [abs_of_neg goldenConj_neg, goldenConj]
    have : (√5 : ℝ) < 2.24 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have h0 : 0 ≤ |goldenConj| := abs_nonneg _
  rw [abs_pow]
  calc |goldenConj| ^ m ≤ |goldenConj| ^ 5 :=
        pow_le_pow_of_le_one h0 (by linarith) hm
    _ < (31 / 50) ^ 5 := by gcongr
    _ < 1 / 10 := by norm_num

/-- `√5 F_m = L_m - 2ψ^m`. -/
theorem s5_fib (m : ℕ) :
    √5 * (Nat.fib m : ℝ) = 2 * (Nat.fib (m + 1) : ℝ) - Nat.fib m - 2 * goldenConj ^ m := by
  rw [← fib_succ_sub_goldenRatio_mul_fib, goldenRatio]; ring

/-- `t² + √5 F t = (-1)^m` for `t = ψ^m`. -/
theorem t_rel (m : ℕ) :
    (goldenConj ^ m) ^ 2 + √5 * (Nat.fib m : ℝ) * goldenConj ^ m = (-1) ^ m := by
  have h := fib_succ_sub_goldenConj_mul_fib m
  have h2 : goldenConj ^ m + √5 * (Nat.fib m : ℝ) = goldenRatio ^ m := by
    rw [← h, s5_fib, ← fib_succ_sub_goldenRatio_mul_fib, goldenRatio, goldenConj]; ring
  calc (goldenConj ^ m) ^ 2 + √5 * (Nat.fib m : ℝ) * goldenConj ^ m
      = goldenConj ^ m * (goldenConj ^ m + √5 * Nat.fib m) := by ring
    _ = (goldenConj * goldenRatio) ^ m := by rw [h2, mul_pow]
    _ = (-1) ^ m := by rw [goldenConj_mul_goldenRatio]

/-- `F_m / φ = F_{m+1} - F_m - ψ^m`. -/
theorem fib_div_gold (m : ℕ) :
    (Nat.fib m : ℝ) / goldenRatio = Nat.fib (m + 1) - Nat.fib m - goldenConj ^ m := by
  rw [div_eq_mul_inv, inv_goldenRatio, ← fib_succ_sub_goldenRatio_mul_fib, ← one_sub_goldenConj]; ring

theorem floor_odd {m : ℕ} (hm : 5 ≤ m) (ho : Odd m) :
    ⌊(Nat.fib m : ℝ) / goldenRatio⌋ = (Nat.fib (m + 1) : ℤ) - Nat.fib m := by
  have ht := t_small hm
  have hneg : goldenConj ^ m < 0 := ho.pow_neg goldenConj_neg
  rw [abs_of_neg hneg] at ht
  rw [Int.floor_eq_iff, fib_div_gold]; push_cast; constructor <;> linarith

theorem floor_even {m : ℕ} (hm : 5 ≤ m) (he : Even m) :
    ⌊(Nat.fib m : ℝ) / goldenRatio⌋ = (Nat.fib (m + 1) : ℤ) - Nat.fib m - 1 := by
  have ht := t_small hm
  have hpos : 0 < goldenConj ^ m := he.pow_pos goldenConj_ne_zero
  rw [abs_of_pos hpos] at ht
  rw [Int.floor_eq_iff, fib_div_gold]; push_cast; constructor <;> linarith

/-- The class identity: for `m ≥ 5` with residues `a = X m mod 20`, `b = Y m mod 20` in `[2, 18]` and
`⌊F/φ⌋ = F_{m+1} - F_m - d`, with `F = F_m`, `t = ψ^m`:
`F (S(F) - ⌊F/φ⌋) = F d + √5 (-a²/200 + a/10 - b²/200 + b/10 - (-1)^m/5 - 1) + √5 t (3a + b - 40)/50`. -/
theorem class_identity {m : ℕ} (hm : 5 ≤ m) (a b : ℤ) (ha : X m % 20 = a) (hb : Y m % 20 = b)
    (ha1 : 2 ≤ a) (ha2 : a ≤ 18) (hb1 : 2 ≤ b) (hb2 : b ≤ 18) (d : ℝ)
    (hfl : (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) = Nat.fib (m + 1) - Nat.fib m - d) :
    (Nat.fib m : ℝ) * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) =
      Nat.fib m * d + √5 * (-(a : ℝ) ^ 2 / 200 + a / 10 - (b : ℝ) ^ 2 / 200 + b / 10 - (-1) ^ m / 5 - 1) +
        √5 * goldenConj ^ m * (3 * a + b - 40) / 50 := by
  set F : ℝ := ((Nat.fib m : ℕ) : ℝ) with hFdef
  set F1 : ℝ := ((Nat.fib (m + 1) : ℕ) : ℝ) with hF1def
  set t : ℝ := goldenConj ^ m with htdef
  have ht := t_small hm
  rw [abs_lt] at ht
  have hsF : √5 * F = 2 * F1 - F - 2 * t := s5_fib m
  have hF4 : 4 ≤ Nat.fib m := (Nat.fib_mono hm).trans' (by norm_num)
  have hF0 : (0 : ℝ) < F := by rw [hFdef]; exact_mod_cast (show 0 < Nat.fib m by omega)
  -- the two integers `qA = (X - a)/20`, `qG = (Y - b)/20`
  obtain ⟨qA, hqA⟩ : ∃ q : ℤ, 20 * q = X m - a := ⟨(X m - a) / 20, by omega⟩
  obtain ⟨qG, hqG⟩ : ∃ q : ℤ, 20 * q = Y m - b := ⟨(Y m - b) / 20, by omega⟩
  have hqAr : 20 * (qA : ℝ) = 6 * F1 - 8 * F + 10 - a := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hqA; unfold X at this; push_cast at this; linarith
  have hqGr : 20 * (qG : ℝ) = 2 * F1 + 4 * F + 10 - b := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hqG; unfold Y at this; push_cast at this; linarith
  have har1 : (2 : ℝ) ≤ a := by exact_mod_cast ha1
  have har2 : (a : ℝ) ≤ 18 := by exact_mod_cast ha2
  have hbr1 : (2 : ℝ) ≤ b := by exact_mod_cast hb1
  have hbr2 : (b : ℝ) ≤ 18 := by exact_mod_cast hb2
  have hαF : α * F = (6 * F1 - 8 * F - 6 * t) / 10 := by rw [α_eq]; linear_combination (3 / 10) * hsF
  have hγF : γ * F = (2 * F1 + 4 * F - 2 * t) / 10 := by rw [γ_eq]; linear_combination (1 / 10) * hsF
  have hqA0 : 0 ≤ qA := by
    have hα0 : 0 ≤ α * F := by
      rw [α_eq]; have := s5_gt; exact mul_nonneg (div_nonneg (by linarith) (by norm_num)) hF0.le
    have : (-1 : ℝ) < qA := by linarith
    have : (-1 : ℤ) < qA := by exact_mod_cast this
    omega
  have hqG0 : 0 ≤ qG := by
    have hγ0 : 0 ≤ γ * F := by rw [γ_eq]; positivity
    have : (-1 : ℝ) < qG := by linarith
    have : (-1 : ℤ) < qG := by exact_mod_cast this
    omega
  obtain ⟨A, rfl⟩ := Int.eq_ofNat_of_zero_le hqA0
  obtain ⟨G, rfl⟩ := Int.eq_ofNat_of_zero_le hqG0
  push_cast at hqAr hqGr
  have hS := S_closed (n := Nat.fib m) (A := A) (G := G) (by omega)
    (by rw [← hFdef]; linarith) (by rw [← hFdef]; linarith)
    (by rw [← hFdef]; linarith) (by rw [← hFdef]; linarith)
  rw [← hFdef] at hS
  have hFS : F * S (Nat.fib m) = F * (3 * A + G) + √5 * (F * (G - A) - 2 * ((A : ℝ) ^ 2 + (G : ℝ) ^ 2)) := by
    rw [hS]; field_simp
  have key := core (√5) F t ((-1) ^ m) (2 * F1 - F) A G (F1 - F - d) a b d s5_sq (by linarith)
    (t_rel m) (by linarith) (by linarith) (by ring)
  rw [hfl, mul_sub, hFS]
  linear_combination key

/-- Bounds used in every class: `F ≥ 5`, `2 < √5 < 9/4`, `|√5 ψ^m| < 1/4`. -/
theorem class_bounds {m : ℕ} (hm : 5 ≤ m) :
    (5 : ℝ) ≤ Nat.fib m ∧ √5 * goldenConj ^ m < 1 / 4 ∧ -(1 / 4) < √5 * goldenConj ^ m := by
  have h5 : 5 ≤ Nat.fib m := (Nat.fib_mono hm).trans' (by norm_num)
  have ht := t_small hm
  have hu : |√5 * goldenConj ^ m| < 1 / 4 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < √5)]
    have := s5_lt
    calc √5 * |goldenConj ^ m| ≤ 9 / 4 * |goldenConj ^ m| := by gcongr
      _ < 9 / 4 * (1 / 10) := by gcongr
      _ < 1 / 4 := by norm_num
  rw [abs_lt] at hu
  exact ⟨by exact_mod_cast h5, hu.2, hu.1⟩

/-- **Zero slack**: `S(F_m) = ⌊F_m/φ⌋` for `m ≥ 5`, `m ≡ 1, 3 (mod 6)` (n = 13, 34, 233, 610, ...). -/
theorem slack_zero {m : ℕ} (hm : 5 ≤ m) (h : m % 6 = 1 ∨ m % 6 = 3) :
    S (Nat.fib m) = ⌊(Nat.fib m : ℝ) / goldenRatio⌋ := by
  have ho : Odd m := Nat.odd_iff.mpr (by omega)
  have hfl : (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) = Nat.fib (m + 1) - Nat.fib m - 0 := by
    rw [floor_odd hm ho]; push_cast; ring
  have hF0 : (Nat.fib m : ℝ) ≠ 0 := by
    have : 0 < Nat.fib m := Nat.fib_pos.mpr (by omega)
    positivity
  suffices hz : (Nat.fib m : ℝ) * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) = 0 by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hF0
    · linarith
  have hab : (X m % 20 = 8 ∧ Y m % 20 = 16) ∨ (X m % 20 = 12 ∧ Y m % 20 = 4) := by
    rw [(XY_mod m).1, (XY_mod m).2]
    have hr : m % 12 = 1 ∨ m % 12 = 3 ∨ m % 12 = 7 ∨ m % 12 = 9 := by omega
    rcases hr with hr | hr | hr | hr <;> rw [hr] <;> decide
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [class_identity hm 8 16 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 hfl,
      ho.neg_one_pow]; push_cast; ring
  · rw [class_identity hm 12 4 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 hfl,
      ho.neg_one_pow]; push_cast; ring

/-- **Negative slack**: `⌊F_m/φ⌋ - 1 < S(F_m) < ⌊F_m/φ⌋` for `m ≥ 5`, `m ≡ 5 (mod 6)` (n = 5, 89, 1597, ...),
so `⌊S(F_m)⌋ = ⌊F_m/φ⌋ - 1`. -/
theorem slack_neg {m : ℕ} (hm : 5 ≤ m) (h : m % 6 = 5) :
    (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) - 1 < S (Nat.fib m) ∧
      S (Nat.fib m) < ⌊(Nat.fib m : ℝ) / goldenRatio⌋ := by
  have ho : Odd m := Nat.odd_iff.mpr (by omega)
  have hfl : (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) = Nat.fib (m + 1) - Nat.fib m - 0 := by
    rw [floor_odd hm ho]; push_cast; ring
  obtain ⟨hF5, hu1, hu2⟩ := class_bounds hm
  have hs1 := s5_gt
  have hs2 := s5_lt
  have hF0 : (0 : ℝ) < Nat.fib m := by linarith
  have hab : (X m % 20 = 18 ∧ Y m % 20 = 6) ∨ (X m % 20 = 2 ∧ Y m % 20 = 14) := by
    rw [(XY_mod m).1, (XY_mod m).2]
    have hr : m % 12 = 5 ∨ m % 12 = 11 := by omega
    rcases hr with hr | hr <;> rw [hr] <;> decide
  suffices hb : (Nat.fib m : ℝ) * (-1) < Nat.fib m * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) ∧
      (Nat.fib m : ℝ) * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) < Nat.fib m * 0 by
    have h1 := lt_of_mul_lt_mul_left hb.1 hF0.le
    have h2 := lt_of_mul_lt_mul_left hb.2 hF0.le
    constructor <;> linarith
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have key := class_identity hm 18 6 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 hfl
    rw [ho.neg_one_pow] at key; norm_num at key
    constructor <;> linarith
  · have key := class_identity hm 2 14 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 hfl
    rw [ho.neg_one_pow] at key; norm_num at key
    constructor <;> linarith

/-- **Even index**: `⌊F_m/φ⌋ < S(F_m) < ⌊F_m/φ⌋ + 1` for even `m ≥ 6` (n = 8, 21, 55, 144, ...). -/
theorem slack_even {m : ℕ} (hm : 6 ≤ m) (he : Even m) :
    (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) < S (Nat.fib m) ∧
      S (Nat.fib m) < ⌊(Nat.fib m : ℝ) / goldenRatio⌋ + 1 := by
  have hm5 : 5 ≤ m := by omega
  have hfl : (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) = Nat.fib (m + 1) - Nat.fib m - 1 := by
    rw [floor_even hm5 he]; push_cast; ring
  obtain ⟨hF5, hu1, hu2⟩ := class_bounds hm5
  have hs1 := s5_gt
  have hs2 := s5_lt
  have hF0 : (0 : ℝ) < Nat.fib m := by linarith
  have hab : (X m % 20 = 16 ∧ Y m % 20 = 12) ∨ (X m % 20 = 14 ∧ Y m % 20 = 18) ∨
      (X m % 20 = 4 ∧ Y m % 20 = 8) ∨ (X m % 20 = 6 ∧ Y m % 20 = 2) := by
    rw [(XY_mod m).1, (XY_mod m).2]
    have hr : m % 12 = 0 ∨ m % 12 = 2 ∨ m % 12 = 4 ∨ m % 12 = 6 ∨ m % 12 = 8 ∨ m % 12 = 10 := by
      obtain ⟨k, hk⟩ := he; omega
    rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr] <;> decide
  suffices hb : (Nat.fib m : ℝ) * 0 < Nat.fib m * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) ∧
      (Nat.fib m : ℝ) * (S (Nat.fib m) - ⌊(Nat.fib m : ℝ) / goldenRatio⌋) < Nat.fib m * 1 by
    have h1 := lt_of_mul_lt_mul_left hb.1 hF0.le
    have h2 := lt_of_mul_lt_mul_left hb.2 hF0.le
    constructor <;> linarith
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have key := class_identity hm5 16 12 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 hfl
    rw [he.neg_one_pow] at key; norm_num at key
    constructor <;> linarith
  · have key := class_identity hm5 14 18 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 hfl
    rw [he.neg_one_pow] at key; norm_num at key
    constructor <;> linarith
  · have key := class_identity hm5 4 8 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 hfl
    rw [he.neg_one_pow] at key; norm_num at key
    constructor <;> linarith
  · have key := class_identity hm5 6 2 ha hb (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 hfl
    rw [he.neg_one_pow] at key; norm_num at key
    constructor <;> linarith

/-- Consequence used with the discrete bound: `⌊S(F_m)⌋ = ⌊F_m/φ⌋ - 1` for `m ≡ 5 (mod 6)`, `m ≥ 5`. -/
theorem floor_S_neg {m : ℕ} (hm : 5 ≤ m) (h : m % 6 = 5) :
    ⌊S (Nat.fib m)⌋ = ⌊(Nat.fib m : ℝ) / goldenRatio⌋ - 1 := by
  obtain ⟨h1, h2⟩ := slack_neg hm h
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

end

end FibSlack

#print axioms FibSlack.slack_zero
#print axioms FibSlack.slack_neg
#print axioms FibSlack.slack_even
#print axioms FibSlack.floor_S_neg
