import QueensLean.OneConflict
import QueensLean.FibSlack

/-!
# The discrete ceiling bound `conf(p) ≤ S(n)`

Lean target 3 (2026-10-18) for "The fewest and the most toroidal conflicts". For an `n`-queens solution `p`
(a permutation of `Fin n` whose flat sums `i + p i` and flat differences `i - p i` are all distinct), the number of
toroidal conflicts `Queens.conf p` (counted per diagonal family, as in `OneConflict.lean`) is at most
`FibSlack.S n = 2 ∑_r g(ρ_r)`. This is the paper's proof of the golden ceiling, before the final convexity step.
With `FibSlack.floor_S_neg` it gives `conf(p) ≤ ⌊F_m/φ⌋ - 1` for `n = F_m`, `m ≡ 5 (mod 6)`, so `C(89) ≤ 54`.
-/

open Finset Real

namespace Ceiling

open Queens FibSlack

/-! ### Counting with weights -/

section counting

variable {n : ℕ}

/-- Number of other rows in the same class as row `i`. -/
def w (f : Fin n → ZMod n) (i : Fin n) : ℕ := #{j | j ≠ i ∧ f j = f i}

/-- Double counting: if every colliding pair has `h i + h j = c`, then `c · pairs f = ∑_i w_i h_i`. -/
theorem pairs_weighted (f : Fin n → ZMod n) (h : Fin n → ℝ) (c : ℝ)
    (hh : ∀ i j, i ≠ j → f i = f j → h i + h j = c) :
    c * pairs f = ∑ i, (w f i : ℝ) * h i := by
  have hw : ∀ i, (w f i : ℝ) * h i = ∑ j, if j ≠ i ∧ f j = f i then h i else 0 := by
    intro i
    unfold w
    rw [natCast_card_filter, sum_mul]
    refine sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  have hp : (pairs f : ℝ) = ∑ i, ∑ j, if i < j ∧ f i = f j then (1 : ℝ) else 0 := by
    unfold pairs
    rw [natCast_card_filter, ← univ_product_univ, sum_product]
  calc c * pairs f = ∑ i, ∑ j, if i < j ∧ f i = f j then h i + h j else 0 := by
        rw [hp, mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        rw [mul_sum]
        refine sum_congr rfl (fun j _ => ?_)
        split_ifs with hc
        · rw [hh i j (ne_of_lt hc.1) hc.2]; ring
        · ring
    _ = (∑ i, ∑ j, if i < j ∧ f i = f j then h i else 0) +
          ∑ i, ∑ j, if i < j ∧ f i = f j then h j else 0 := by
        rw [← sum_add_distrib]
        refine sum_congr rfl (fun i _ => ?_)
        rw [← sum_add_distrib]
        refine sum_congr rfl (fun j _ => ?_)
        split_ifs <;> ring
    _ = (∑ i, ∑ j, if i < j ∧ f i = f j then h i else 0) +
          ∑ i, ∑ j, if j < i ∧ f j = f i then h i else 0 := by
        rw [sum_comm (s := univ) (t := univ) (f := fun i j => if i < j ∧ f i = f j then h j else 0)]
    _ = ∑ i, (w f i : ℝ) * h i := by
        rw [← sum_add_distrib]
        refine sum_congr rfl (fun i _ => ?_)
        rw [hw, ← sum_add_distrib]
        refine sum_congr rfl (fun j _ => ?_)
        rcases lt_trichotomy i j with hij | hij | hij
        · have h1 : ¬ j < i := not_lt.mpr hij.le
          have h2 : j ≠ i := ne_of_gt hij
          by_cases hf : f j = f i
          · simp [hij, h1, h2, hf]
          · have hf' : ¬ f i = f j := fun e => hf e.symm
            simp [hf, hf', h1]
        · subst hij; simp
        · have h1 : ¬ i < j := not_lt.mpr hij.le
          have h2 : j ≠ i := ne_of_lt hij
          by_cases hf : f j = f i
          · simp [hij, h1, h2, hf]
          · simp [hf, h1]

/-- Values in a window of width `2n - 2` that agree mod `n` and differ are exactly `n` apart. -/
theorem gap {v : Fin n → ℤ} (hv : Function.Injective v) (lo : ℤ)
    (hlo : ∀ i, lo ≤ v i ∧ v i ≤ lo + 2 * n - 2) {i j : Fin n} (hij : i ≠ j)
    (hd : (n : ℤ) ∣ v j - v i) : v j = v i + n ∨ v i = v j + n := by
  obtain ⟨k, hk⟩ := hd
  have hne : v i ≠ v j := fun e => hij (hv e)
  have hi := hlo i
  have hj := hlo j
  have hn : (0 : ℤ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact i.elim0
    · exact_mod_cast h0
  have hk1 : k < 2 := by nlinarith
  have hk2 : -2 < k := by nlinarith
  interval_cases k
  · right; linarith
  · exact absurd (by linarith) hne
  · left; linarith

/-- In a window of width `2n - 2`, a class holds at most two of the values: at most one partner. -/
theorem w_le_one {f : Fin n → ZMod n} {v : Fin n → ℤ} (hv : Function.Injective v) (lo : ℤ)
    (hlo : ∀ i, lo ≤ v i ∧ v i ≤ lo + 2 * n - 2) (hf : ∀ i j, f i = f j → (n : ℤ) ∣ v j - v i)
    (i : Fin n) : w f i ≤ 1 := by
  unfold w
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  by_contra hab
  have g1 := gap hv lo hlo ha.1 (hf a i ha.2)
  have g2 := gap hv lo hlo hb.1 (hf b i hb.2)
  have hne : v a ≠ v b := fun e => hab (hv e)
  have h1 := hlo a
  have h2 := hlo b
  omega

/-- Lemma `dist`: the two queens of a conflict sit at total distance `n` from the middle value `lo + n - 1`. -/
theorem dist {v : Fin n → ℤ} (hv : Function.Injective v) (lo : ℤ)
    (hlo : ∀ i, lo ≤ v i ∧ v i ≤ lo + 2 * n - 2) {i j : Fin n} (hij : i ≠ j)
    (hd : (n : ℤ) ∣ v j - v i) : |v i - (lo + n - 1)| + |v j - (lo + n - 1)| = n := by
  have h1 := hlo i
  have h2 := hlo j
  rcases gap hv lo hlo hij hd with h | h <;>
    rcases abs_cases (v i - (lo + n - 1)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases (v j - (lo + n - 1)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega

end counting

/-! ### The function `g` from below -/

theorem s5_pos : (0 : ℝ) < √5 := by positivity

theorem s5_α : √5 * α = (15 - 5 * √5) / 10 := by rw [α_eq]; linear_combination (3 / 10) * s5_sq

theorem s5_γ : √5 * γ = (5 + 5 * √5) / 10 := by rw [γ_eq]; linear_combination (1 / 10) * s5_sq

theorem g_nonneg (x : ℝ) : 0 ≤ g x := by
  have h1 := s5_gt
  unfold g
  split_ifs with hα hγ
  · have := mul_le_mul_of_nonneg_left hα s5_pos.le
    rw [s5_α] at this; linarith
  · exact mul_nonneg (by positivity) (by linarith)
  · exact le_refl 0

theorem g_ge_lin (x : ℝ) : 1 - √5 * x ≤ g x := by
  have h1 := s5_gt
  unfold g
  split_ifs with hα hγ
  · exact le_refl _
  · have := mul_le_mul_of_nonneg_left (not_le.mp hα).le s5_pos.le
    rw [s5_α] at this
    have e : √5 / 2 * (γ - x) = √5 * γ / 2 - √5 * x / 2 := by ring
    rw [e, s5_γ]; linarith
  · have := mul_le_mul_of_nonneg_left (not_le.mp hγ).le s5_pos.le
    rw [s5_γ] at this; linarith

theorem g_ge_k (x : ℝ) : √5 / 2 * (γ - x) ≤ g x := by
  have h1 := s5_gt
  have e : √5 / 2 * (γ - x) = √5 * γ / 2 - √5 * x / 2 := by ring
  unfold g
  split_ifs with hα hγ
  · have := mul_le_mul_of_nonneg_left hα s5_pos.le
    rw [s5_α] at this
    rw [e, s5_γ]; linarith
  · exact le_refl _
  · have := mul_le_mul_of_nonneg_left (not_le.mp hγ).le s5_pos.le
    rw [s5_γ] at this
    rw [e, s5_γ]; linarith

/-! ### One queen -/

/-- The bound for one queen in row `r`, column `c`, with `ws`, `wd ∈ {0, 1}` partners in the two families:
`(1 - √5)(ws + wd)/2 + √5 (ws |u| + wd |t|)/N ≤ g(ρ_r) + g(ρ_c)`, `u = r + c - (N - 1)`, `t = r - c`. -/
theorem queen_bound (N r c ws wd : ℝ) (hN : 0 < N) (hws : ws = 0 ∨ ws = 1) (hwd : wd = 0 ∨ wd = 1) :
    (1 - √5) / 2 * (ws + wd) + √5 / N * (ws * |r + c - (N - 1)| + wd * |r - c|) ≤
      g ((N - |2 * r - (N - 1)|) / N) + g ((N - |2 * c - (N - 1)|) / N) := by
  set x := r - (N - 1) / 2 with hx
  set y := c - (N - 1) / 2 with hy
  have e1 : r + c - (N - 1) = x + y := by rw [hx, hy]; ring
  have e2 : r - c = x - y := by rw [hx, hy]; ring
  have e3 : (N - |2 * r - (N - 1)|) / N = 1 - 2 * (|x| / N) := by
    rw [show 2 * r - (N - 1) = 2 * x by rw [hx]; ring, abs_mul, abs_two]; field_simp
  have e4 : (N - |2 * c - (N - 1)|) / N = 1 - 2 * (|y| / N) := by
    rw [show 2 * c - (N - 1) = 2 * y by rw [hy]; ring, abs_mul, abs_two]; field_simp
  have hN0 : 0 ≤ N := hN.le
  -- everything in the four quotients `a = |x|/N`, `b = |y|/N`, `P = |x+y|/N`, `Q = |x-y|/N`
  have hP : |x + y| / N ≤ |x| / N + |y| / N := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (abs_add_le x y) hN0
  have hQ : |x - y| / N ≤ |x| / N + |y| / N := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (abs_sub x y) hN0
  have hPQ : |x + y| / N + |x - y| / N ≤ 2 * (|x| / N) ∨ |x + y| / N + |x - y| / N ≤ 2 * (|y| / N) := by
    rw [← add_div, ← mul_div_assoc, ← mul_div_assoc]
    have key : |x + y| + |x - y| ≤ 2 * |x| ∨ |x + y| + |x - y| ≤ 2 * |y| := by
      rcases abs_cases (x + y) with ⟨a1, _⟩ | ⟨a1, _⟩ <;> rcases abs_cases (x - y) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
        rcases abs_cases x with ⟨a3, _⟩ | ⟨a3, _⟩ <;> rcases abs_cases y with ⟨a4, _⟩ | ⟨a4, _⟩ <;>
        first | (left; linarith) | (right; linarith)
    rcases key with k | k
    · left; exact div_le_div_of_nonneg_right k hN0
    · right; exact div_le_div_of_nonneg_right k hN0
  have hgoal : √5 / N * (ws * |x + y| + wd * |x - y|) = √5 * (ws * (|x + y| / N) + wd * (|x - y| / N)) := by
    ring
  rw [e1, e2, e3, e4, hgoal]
  generalize |x| / N = a at *
  generalize |y| / N = b at *
  generalize |x + y| / N = P at *
  generalize |x - y| / N = Q at *
  have hs1 := s5_gt
  have hsγ := s5_γ
  have k1 := g_ge_k (1 - 2 * a)
  have k2 := g_ge_k (1 - 2 * b)
  have l1 := g_ge_lin (1 - 2 * a)
  have l2 := g_ge_lin (1 - 2 * b)
  have n1 := g_nonneg (1 - 2 * a)
  have n2 := g_nonneg (1 - 2 * b)
  have mP := mul_le_mul_of_nonneg_left hP s5_pos.le
  have mQ := mul_le_mul_of_nonneg_left hQ s5_pos.le
  rcases hws with rfl | rfl <;> rcases hwd with rfl | rfl
  · linarith
  · linarith
  · linarith
  · rcases hPQ with h | h
    · have := mul_le_mul_of_nonneg_left h s5_pos.le
      linarith
    · have := mul_le_mul_of_nonneg_left h s5_pos.le
      linarith

/-! ### The bound -/

section bound

variable {n : ℕ}

/-- `S(n) = ∑_i (g(ρ_i) + g(ρ_{p i}))` for any permutation `p`. -/
theorem S_perm (p : Equiv.Perm (Fin n)) :
    S n = ∑ i : Fin n, (g (ρ n i) + g (ρ n (p i))) := by
  rw [sum_add_distrib, Equiv.sum_comp p (fun j : Fin n => g (ρ n j)),
    Fin.sum_univ_eq_sum_range (fun r => g (ρ n r)) n]
  unfold S; ring

/-- Flat sum and flat difference of row `i`. -/
def vs (p : Equiv.Perm (Fin n)) (i : Fin n) : ℤ := (i : ℕ) + ((p i : ℕ) : ℤ)
def vd (p : Equiv.Perm (Fin n)) (i : Fin n) : ℤ := (i : ℕ) - ((p i : ℕ) : ℤ)

theorem vs_range (p : Equiv.Perm (Fin n)) (i : Fin n) : 0 ≤ vs p i ∧ vs p i ≤ 0 + 2 * n - 2 := by
  unfold vs; have := i.isLt; have := (p i).isLt; omega

theorem vd_range (p : Equiv.Perm (Fin n)) (i : Fin n) :
    -((n : ℤ) - 1) ≤ vd p i ∧ vd p i ≤ -((n : ℤ) - 1) + 2 * n - 2 := by
  unfold vd; have := i.isLt; have := (p i).isLt; omega

theorem sum_dvd (p : Equiv.Perm (Fin n)) (i j : Fin n) (h : sumCls p i = sumCls p j) :
    (n : ℤ) ∣ vs p j - vs p i := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  unfold vs; push_cast; exact h

theorem dif_dvd (p : Equiv.Perm (Fin n)) (i j : Fin n) (h : difCls p i = difCls p j) :
    (n : ℤ) ∣ vd p j - vd p i := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  unfold vd; push_cast; exact h

theorem w01 {f : Fin n → ZMod n} {i : Fin n} (h : w f i ≤ 1) : (w f i : ℝ) = 0 ∨ (w f i : ℝ) = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h <;> simp [h]

/-- **Discrete ceiling**: every `n`-queens solution has at most `S(n)` toroidal conflicts. -/
theorem conf_le_S [NeZero n] (p : Equiv.Perm (Fin n)) (hs : Function.Injective (vs p))
    (hd : Function.Injective (vd p)) : (conf p : ℝ) ≤ S n := by
  set N : ℝ := (n : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set hS : Fin n → ℝ := fun i => |((i : ℕ) : ℝ) + ((p i : ℕ) : ℝ) - (N - 1)| with hSdef
  set hD : Fin n → ℝ := fun i => |((i : ℕ) : ℝ) - ((p i : ℕ) : ℝ)| with hDdef
  have e2s := pairs_weighted (sumCls p) (fun _ => 1) 2 (fun _ _ _ _ => by norm_num)
  have e2d := pairs_weighted (difCls p) (fun _ => 1) 2 (fun _ _ _ _ => by norm_num)
  simp only [mul_one] at e2s e2d
  have eNs := pairs_weighted (sumCls p) hS N (by
    intro i j hij hf
    have hz := dist hs 0 (vs_range p) hij (sum_dvd p i j hf)
    have := congrArg (fun z : ℤ => (z : ℝ)) hz
    simp only [vs] at this; push_cast at this
    rw [show (0 : ℝ) + n - 1 = n - 1 by ring] at this
    simp only [hSdef, hNdef]; exact this)
  have eNd := pairs_weighted (difCls p) hD N (by
    intro i j hij hf
    have hz := dist hd (-((n : ℤ) - 1)) (vd_range p) hij (dif_dvd p i j hf)
    have := congrArg (fun z : ℤ => (z : ℝ)) hz
    simp only [vd] at this; push_cast at this
    rw [show -((n : ℝ) - 1) + n - 1 = 0 by ring, sub_zero, sub_zero] at this
    simp only [hDdef, hNdef]; exact this)
  have hq : ∀ i ∈ (univ : Finset (Fin n)),
      (1 - √5) / 2 * ((w (sumCls p) i : ℝ) + w (difCls p) i) +
        √5 / N * ((w (sumCls p) i : ℝ) * hS i + (w (difCls p) i : ℝ) * hD i) ≤
      g (ρ n i) + g (ρ n (p i)) := by
    intro i _
    exact queen_bound N _ _ _ _ hN (w01 (w_le_one hs 0 (vs_range p) (sum_dvd p) i))
      (w01 (w_le_one hd _ (vd_range p) (dif_dvd p) i))
  have hsum := sum_le_sum hq
  rw [← S_perm p] at hsum
  have hconf : ∑ i : Fin n, ((1 - √5) / 2 * ((w (sumCls p) i : ℝ) + w (difCls p) i) +
      √5 / N * ((w (sumCls p) i : ℝ) * hS i + (w (difCls p) i : ℝ) * hD i)) = conf p := by
    simp only [mul_add, sum_add_distrib, ← mul_sum]
    rw [← e2s, ← e2d, ← eNs, ← eNd]
    unfold conf; push_cast
    field_simp
    ring
  linarith

end bound

/-! ### Consequences at Fibonacci sizes -/

/-- For `n = F_m`, `m ≥ 5`, `m ≡ 5 (mod 6)`, every solution has at most `⌊F_m/φ⌋ - 1` toroidal conflicts. -/
theorem conf_le_fib {m : ℕ} (hm : 5 ≤ m) (h6 : m % 6 = 5) {n : ℕ} [NeZero n] (hn : n = Nat.fib m)
    (p : Equiv.Perm (Fin n)) (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) :
    (conf p : ℤ) ≤ ⌊(Nat.fib m : ℝ) / goldenRatio⌋ - 1 := by
  rw [← floor_S_neg hm h6, Int.le_floor, ← hn]
  exact_mod_cast conf_le_S p hs hd

/-- **`C(89) ≤ 54`**: no 89-queens solution has more than 54 toroidal conflicts. -/
theorem conf_le_54 (p : Equiv.Perm (Fin 89)) (hs : Function.Injective (vs p))
    (hd : Function.Injective (vd p)) : conf p ≤ 54 := by
  have h := conf_le_fib (m := 11) (by norm_num) (by norm_num) (by decide) p hs hd
  rw [floor_odd (by norm_num) (by decide)] at h
  have e1 : Nat.fib 12 = 144 := by decide
  have e2 : Nat.fib 11 = 89 := by decide
  rw [e1, e2] at h
  omega

end Ceiling

#print axioms Ceiling.conf_le_S
#print axioms Ceiling.conf_le_54
