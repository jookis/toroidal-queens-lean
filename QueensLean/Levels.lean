import QueensLean.LowerBound

/-!
# Forbidden levels

Lean target (2026-10-18) for Theorem `thm:levels` of "The fewest and the most toroidal conflicts". For every
permutation `p` of `Fin n` (so for every `n`-queens solution), conflicts counted toroidally per family:

1. `conf p ≠ 1` (`Queens.conf_ne_one`);
2. `conf p ≠ 2` if `n ≥ 5` is prime (`conf_ne_two_prime`);
3. `conf p ≠ 3` if `n = 2q` with `q ≥ 5` prime (`conf_ne_three`).

Tools: `cnt f r` rows in class `r`; `e f r = cnt f r - 1` has sum `0` and sum of squares `2 · pairs f`, so a family
with two colliding pairs has two doubled classes `a, b` and two missing `m₁, m₂`, all distinct (`pairs_two_phi`).
Equal sums and sums of squares in a field force `{a, b} = {m₁, m₂}` (`quad`).
-/

open Finset

namespace Levels

open Queens Lower

variable {n : ℕ} [NeZero n]

/-- Number of rows in class `r`. -/
def cnt (f : Fin n → ZMod n) (r : ZMod n) : ℕ := (univ.filter (fun i => f i = r)).card

theorem sum_cnt {M : Type*} [AddCommMonoid M] (f : Fin n → ZMod n) (φ : ZMod n → M) :
    ∑ i, φ (f i) = ∑ r, cnt f r • φ r := by
  rw [← sum_fiberwise univ f (fun i => φ (f i))]
  refine sum_congr rfl (fun r _ => ?_)
  rw [sum_congr rfl (fun i hi => congrArg φ (mem_filter.mp hi).2), sum_const]
  rfl

omit [NeZero n] in
theorem pairs_sum (f : Fin n → ZMod n) :
    pairs f = ∑ i, ∑ j, if i < j ∧ f i = f j then 1 else 0 := by
  unfold pairs
  rw [card_filter, ← univ_product_univ, sum_product]

theorem sum_cnt_sq (f : Fin n → ZMod n) : ∑ r, cnt f r ^ 2 = n + 2 * pairs f := by
  have h1 : ∑ r, cnt f r ^ 2 = ∑ i, cnt f (f i) := by
    rw [sum_cnt f (cnt f)]; simp [sq, smul_eq_mul]
  have h2 : ∀ i, cnt f (f i) = ∑ j, if f j = f i then 1 else 0 := by
    intro i; unfold cnt; rw [card_filter]
  have h3 : ∀ i j : Fin n, (if f j = f i then 1 else 0) = (if i < j ∧ f i = f j then 1 else 0) +
      (if i = j then 1 else 0) + (if j < i ∧ f j = f i then 1 else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · by_cases hf : f i = f j
      · simp [h, hf, h.ne, not_lt.mpr h.le]
      · have hf' : ¬ f j = f i := fun e => hf e.symm
        simp [h, hf, hf', h.ne, not_lt.mpr h.le]
    · simp
    · by_cases hf : f j = f i
      · simp [h, hf, h.ne', not_lt.mpr h.le]
      · have hf' : ¬ f i = f j := fun e => hf e.symm
        simp [h, hf, hf', h.ne', not_lt.mpr h.le]
  rw [h1, pairs_sum]
  simp_rw [h2, h3, sum_add_distrib]
  rw [sum_comm (f := fun i j => if j < i ∧ f j = f i then 1 else 0)]
  simp
  ring

/-- Excess of class `r`: rows in it minus one. -/
def e (f : Fin n → ZMod n) (r : ZMod n) : ℤ := (cnt f r : ℤ) - 1

omit [NeZero n] in
theorem e_ge (f : Fin n → ZMod n) (r : ZMod n) : -1 ≤ e f r := by unfold e; omega

theorem sum_cnt_eq (f : Fin n → ZMod n) : ∑ r, (cnt f r : ℤ) = n := by
  have h := sum_cnt f (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h.symm

theorem sum_e (f : Fin n → ZMod n) : ∑ r, e f r = 0 := by
  unfold e
  rw [sum_sub_distrib, sum_cnt_eq]
  simp [ZMod.card]

theorem sum_e_sq (f : Fin n → ZMod n) : ∑ r, e f r ^ 2 = 2 * (pairs f : ℤ) := by
  have hq : ∑ r, (cnt f r : ℤ) ^ 2 = n + 2 * pairs f := by exact_mod_cast sum_cnt_sq f
  have hx : ∀ r, e f r ^ 2 = (cnt f r : ℤ) ^ 2 - 2 * (cnt f r : ℤ) + 1 := by intro r; unfold e; ring
  simp_rw [hx]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hq, sum_cnt_eq]
  simp [ZMod.card]
  ring

/-- Integers `≥ -1` with sum `0` and sum of squares `4`: two `+1` and two `-1`, the rest `0`. -/
theorem four {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R] (e : α → ℤ) (hl : ∀ r, -1 ≤ e r)
    (hs : ∑ r, e r = 0) (hq : ∑ r, e r ^ 2 = 4) :
    ∃ a b m1 m2 : α, a ≠ b ∧ m1 ≠ m2 ∧ a ≠ m1 ∧ a ≠ m2 ∧ b ≠ m1 ∧ b ≠ m2 ∧
      ∀ φ : α → R, ∑ r, (e r : R) * φ r = φ a + φ b - φ m1 - φ m2 := by
  have hle : ∀ r, e r ^ 2 ≤ 4 := fun r =>
    hq ▸ single_le_sum (f := fun i => e i ^ 2) (fun i _ => sq_nonneg (e i)) (mem_univ r)
  have hne2 : ∀ r, e r ≠ 2 := by
    intro r hr
    have h1 := add_sum_erase univ (fun x => e x ^ 2) (mem_univ r)
    have h2 := add_sum_erase univ e (mem_univ r)
    rw [hr] at h1 h2
    have h0 : ∀ x ∈ univ.erase r, e x ^ 2 = 0 := by
      have : ∑ x ∈ univ.erase r, e x ^ 2 = 0 := by linarith
      exact (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (e i))).mp this
    have : ∑ x ∈ univ.erase r, e x = 0 := sum_eq_zero (fun x hx => pow_eq_zero_iff two_ne_zero |>.mp (h0 x hx))
    linarith
  have h3 : ∀ r, e r = -1 ∨ e r = 0 ∨ e r = 1 := by
    intro r
    have := hl r; have := hle r; have := hne2 r
    have : e r ≤ 2 := by nlinarith
    omega
  have hpt : ∀ r, e r = (if e r = 1 then 1 else 0) - (if e r = -1 then 1 else 0) := by
    intro r; rcases h3 r with h | h | h <;> simp [h]
  have hpt2 : ∀ r, e r ^ 2 = (if e r = 1 then 1 else 0) + (if e r = -1 then 1 else 0) := by
    intro r; rcases h3 r with h | h | h <;> simp [h]
  have hs' : ∑ r, e r = ∑ r, ((if e r = 1 then (1 : ℤ) else 0) - (if e r = -1 then 1 else 0)) :=
    sum_congr rfl (fun r _ => hpt r)
  have hq' : ∑ r, e r ^ 2 = ∑ r, ((if e r = 1 then (1 : ℤ) else 0) + (if e r = -1 then 1 else 0)) :=
    sum_congr rfl (fun r _ => hpt2 r)
  rw [sum_sub_distrib, sum_boole, sum_boole] at hs'
  rw [sum_add_distrib, sum_boole, sum_boole] at hq'
  have hA : (univ.filter (fun r => e r = 1)).card = 2 := by
    have : ((univ.filter (fun r => e r = 1)).card : ℤ) = 2 := by linarith
    exact_mod_cast this
  have hM : (univ.filter (fun r => e r = -1)).card = 2 := by
    have : ((univ.filter (fun r => e r = -1)).card : ℤ) = 2 := by linarith
    exact_mod_cast this
  obtain ⟨a, b, hab, hAe⟩ := card_eq_two.mp hA
  obtain ⟨m1, m2, hm, hMe⟩ := card_eq_two.mp hM
  have mA : ∀ x ∈ ({a, b} : Finset α), e x = 1 := fun x hx => by
    rw [← hAe] at hx; exact (mem_filter.mp hx).2
  have mM : ∀ x ∈ ({m1, m2} : Finset α), e x = -1 := fun x hx => by
    rw [← hMe] at hx; exact (mem_filter.mp hx).2
  have ea := mA a (by simp)
  have eb := mA b (by simp)
  have em1 := mM m1 (by simp)
  have em2 := mM m2 (by simp)
  have ne : ∀ x y, e x = 1 → e y = -1 → x ≠ y := fun x y hx hy hxy => by rw [hxy] at hx; omega
  refine ⟨a, b, m1, m2, hab, hm, ne _ _ ea em1, ne _ _ ea em2, ne _ _ eb em1, ne _ _ eb em2, fun φ => ?_⟩
  have hφ : ∀ r, (e r : R) * φ r = (if e r = 1 then φ r else 0) - (if e r = -1 then φ r else 0) := by
    intro r; rcases h3 r with h | h | h <;> simp [h]
  rw [sum_congr rfl (fun r _ => hφ r), sum_sub_distrib, ← sum_filter, ← sum_filter, hAe, hMe,
    sum_pair hab, sum_pair hm]
  ring

/-- **Two colliding pairs**: two doubled classes `a, b`, two missing `m₁, m₂`, all four distinct. -/
theorem pairs_two_phi (f : Fin n → ZMod n) (h : pairs f = 2) :
    ∃ a b m1 m2 : ZMod n, a ≠ b ∧ m1 ≠ m2 ∧ a ≠ m1 ∧ a ≠ m2 ∧ b ≠ m1 ∧ b ≠ m2 ∧
      ∀ φ : ZMod n → ZMod n, ∑ i, φ (f i) = ∑ r, φ r + φ a + φ b - φ m1 - φ m2 := by
  obtain ⟨a, b, m1, m2, h1, h2, h3, h4, h5, h6, hφ⟩ :=
    four (R := ZMod n) (e f) (e_ge f) (sum_e f) (by rw [sum_e_sq, h]; norm_num)
  refine ⟨a, b, m1, m2, h1, h2, h3, h4, h5, h6, fun φ => ?_⟩
  rw [sum_cnt f φ]
  have hx : ∀ r, cnt f r • φ r = φ r + (e f r : ZMod n) * φ r := by
    intro r; unfold e; rw [nsmul_eq_mul]; push_cast; ring
  simp_rw [hx]
  rw [sum_add_distrib, hφ]
  ring

/-- Equal sums and sums of squares of two pairs in a field (with `2 ≠ 0`): the pairs share an element. -/
theorem quad {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {a b m1 m2 : F} (hs : a + b = m1 + m2)
    (hq : a ^ 2 + b ^ 2 = m1 ^ 2 + m2 ^ 2) : a = m1 ∨ a = m2 := by
  have hp : a * b = m1 * m2 := by
    have : 2 * (a * b) = 2 * (m1 * m2) := by linear_combination (a + b + m1 + m2) * hs - hq
    exact mul_left_cancel₀ h2 this
  have : (a - m1) * (a - m2) = 0 := by linear_combination a * hs - hp
  rcases mul_eq_zero.mp this with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

omit [NeZero n] in
theorem natCast_ne {m k : ℕ} (hk0 : 0 < k) (hk : k < m) : (k : ZMod m) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hk0 h0
  omega

omit [NeZero n] in
/-- `2Q ≡ 0 (mod m)` for a prime `m ≥ 5` dividing `n`. -/
theorem two_Q_zero {m : ℕ} (hp : m.Prime) (h5 : 5 ≤ m) (hm : m ∣ n) : 2 * ((Q n : ℕ) : ZMod m) = 0 := by
  have := Fact.mk hp
  have h6 := six_Q n
  have hc : ((6 * (Q n : ℤ) : ℤ) : ZMod m) = ((n * ((n : ℤ) - 1) * (2 * n - 1) : ℤ) : ZMod m) := by rw [h6]
  push_cast at hc
  rw [(ZMod.natCast_eq_zero_iff n m).mpr hm, zero_mul, zero_mul] at hc
  have h3 : (3 : ZMod m) ≠ 0 := by exact_mod_cast natCast_ne (m := m) (k := 3) (by norm_num) (by omega)
  have : (3 : ZMod m) * (2 * (Q n : ZMod m)) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h3
  · exact h

/-- A family with two colliding pairs, sum `0` and sum of squares `3Q`, is impossible for prime `n ≥ 5`. -/
theorem two_family_prime (hp : n.Prime) (h5 : 5 ≤ n) (g : Fin n → ZMod n) (hg : pairs g = 2)
    (hs : ∑ i, g i = 0) (hq : ∑ i, g i ^ 2 = 3 * ((Q n : ℕ) : ZMod n)) : False := by
  have := Fact.mk hp
  have ho : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h2 : (2 : ZMod n) ≠ 0 := by exact_mod_cast natCast_ne (m := n) (k := 2) (by norm_num) (by omega)
  have h2Q := two_Q_zero hp h5 (dvd_refl n)
  obtain ⟨a, b, m1, m2, -, -, h3, h4, -, -, hφ⟩ := pairs_two_phi g hg
  have e1 := hφ id
  have e2 := hφ (fun r => r ^ 2)
  simp only [id] at e1 e2
  rw [← T_eq_sum, T_odd ho] at e1
  rw [res_sq] at e2
  rcases quad (a := a) (b := b) (m1 := m1) (m2 := m2) h2 (by linear_combination hs - e1) (by linear_combination hq - e2 + h2Q) with h | h
  · exact h3 h
  · exact h4 h

/-- **Theorem `thm:levels` (2)**: no permutation has exactly two toroidal conflicts when `n ≥ 5` is prime. -/
theorem conf_ne_two_prime (p : Equiv.Perm (Fin n)) (hp : n.Prime) (h5 : 5 ≤ n) : conf p ≠ 2 := by
  intro hc
  unfold conf at hc
  have ho : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hT := T_odd ho
  have hS : ∑ i, sumCls p i = 0 := by rw [sum_sumCls, hT, mul_zero]
  have hD : ∑ i, difCls p i = 0 := sum_difCls p
  have hsq := sq_sum p
  rcases (by omega : pairs (sumCls p) = 0 ∧ pairs (difCls p) = 2 ∨ pairs (sumCls p) = 1 ∨
      pairs (sumCls p) = 2 ∧ pairs (difCls p) = 0) with ⟨h0, h2⟩ | h1 | ⟨h2, h0⟩
  · have a1 := complete_family h0 (fun r => r ^ 2)
    rw [res_sq] at a1
    exact two_family_prime hp h5 _ h2 hD (by linear_combination hsq - a1)
  · obtain ⟨a, m, ham, hφ⟩ := pairs_one_phi _ h1
    have e1 := hφ id
    simp only [id] at e1
    rw [← T_eq_sum, hT, hS] at e1
    exact ham (by linear_combination -e1)
  · have a1 := complete_family h0 (fun r => r ^ 2)
    rw [res_sq] at a1
    exact two_family_prime hp h5 _ h2 hS (by linear_combination hsq - a1)

/-- Lifting: for `n = 2q`, a nonzero class that vanishes modulo `q` is `q`. -/
theorem lift_q {q : ℕ} (hn : n = 2 * q) (u : ZMod n) (hu : u ≠ 0)
    (hψ : ZMod.castHom (show q ∣ n from ⟨2, by omega⟩) (ZMod q) u = 0) : u = (q : ZMod n) := by
  have hv := ZMod.natCast_zmod_val u
  rw [← hv, map_natCast, ZMod.natCast_eq_zero_iff] at hψ
  have hlt := ZMod.val_lt u
  have h0 : u.val ≠ 0 := fun h => hu ((ZMod.val_eq_zero u).mp h)
  obtain ⟨k, hk⟩ := hψ
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; rw [zero_mul] at hk; exact absurd hk h0
    · exact h
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · rw [mul_zero] at hk; exact absurd hk h0
    · rfl
    · exfalso; rw [hk, hn] at hlt; nlinarith
  rw [← hv, hk, hk1, mul_one]

/-- One family with one colliding pair and one with two, for `n = 2q`, `q ≥ 5` prime: impossible. -/
theorem one_two {q : ℕ} (hqp : q.Prime) (h5 : 5 ≤ q) (hn : n = 2 * q) (f g : Fin n → ZMod n)
    (hf : pairs f = 1) (hg : pairs g = 2) (hsf : ∑ i, f i = 0) (hsg : ∑ i, g i = 0)
    (hsq : ∑ i, f i ^ 2 + ∑ i, g i ^ 2 = 4 * ((Q n : ℕ) : ZMod n)) : False := by
  have := Fact.mk hqp
  have hqn : q ∣ n := ⟨2, by omega⟩
  set ψ := ZMod.castHom hqn (ZMod q) with hψdef
  have he : n % 2 = 0 := by omega
  have hTne := T_even he
  have hψT : ψ (T n) = 0 := by
    rw [T_cast, sum_range_id]
    have : n * (n - 1) / 2 = q * (n - 1) := by
      rw [hn, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [this, map_natCast]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have h2Q : 2 * ((Q n : ℕ) : ZMod q) = 0 := two_Q_zero hqp h5 hqn
  have h2 : (2 : ZMod q) ≠ 0 := by exact_mod_cast natCast_ne (m := q) (k := 2) (by norm_num) (by omega)
  obtain ⟨a, m, -, hφ⟩ := pairs_one_phi f hf
  have e1 := hφ id
  have e2 := hφ (fun r => r ^ 2)
  simp only [id] at e1 e2
  rw [← T_eq_sum] at e1
  rw [res_sq] at e2
  obtain ⟨a', b', m1, m2, -, -, h3, h4, h5', h6, hχ⟩ := pairs_two_phi g hg
  have e3 := hχ id
  have e4 := hχ (fun r => r ^ 2)
  simp only [id] at e3 e4
  rw [← T_eq_sum] at e3
  rw [res_sq] at e4
  -- the defect equations in `ZMod n`
  have hA : a = m - T n := by linear_combination hsf - e1
  have hS2 : a' + b' - m1 - m2 = -T n := by linear_combination hsg - e3
  have hQ2 : a' ^ 2 + b' ^ 2 - m1 ^ 2 - m2 ^ 2 = 2 * ((Q n : ℕ) : ZMod n) + 2 * m * T n - T n ^ 2 := by
    rw [hA] at e2; linear_combination hsq - e2 - e4
  -- reduce modulo `q`
  have mS := congrArg ψ hS2
  have mQ := congrArg ψ hQ2
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_natCast, map_ofNat, hψT] at mS mQ
  have hs' : ψ a' + ψ b' = ψ m1 + ψ m2 := by linear_combination mS
  have hq' : ψ a' ^ 2 + ψ b' ^ 2 = ψ m1 ^ 2 + ψ m2 ^ 2 := by linear_combination mQ + h2Q
  have hqq : (q : ZMod n) + q = 0 := by
    have : ((2 * q : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
    push_cast at this; linear_combination this
  rcases quad h2 hs' hq' with h | h
  · have hb : ψ (b' - m2) = 0 := by rw [map_sub]; linear_combination hs' - h
    have u := lift_q hn (a' - m1) (sub_ne_zero.mpr h3) (by rw [map_sub, h, sub_self])
    have v := lift_q hn (b' - m2) (sub_ne_zero.mpr h6) hb
    exact hTne (by linear_combination hS2 - u - v - hqq)
  · have hb : ψ (b' - m1) = 0 := by rw [map_sub]; linear_combination hs' - h
    have u := lift_q hn (a' - m2) (sub_ne_zero.mpr h4) (by rw [map_sub, h, sub_self])
    have v := lift_q hn (b' - m1) (sub_ne_zero.mpr h5') hb
    exact hTne (by linear_combination hS2 - u - v - hqq)

/-- **Theorem `thm:levels` (3)**: no permutation has exactly three toroidal conflicts when `n = 2q` with
`q ≥ 5` prime. -/
theorem conf_ne_three (p : Equiv.Perm (Fin n)) {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (hn : n = 2 * q) :
    conf p ≠ 3 := by
  intro hc
  unfold conf at hc
  have he : n % 2 = 0 := by omega
  obtain ⟨hs0, hd0⟩ := even_no_free p he
  have hS : ∑ i, sumCls p i = 0 := by rw [sum_sumCls, two_T]
  have hD : ∑ i, difCls p i = 0 := sum_difCls p
  have hsq := sq_sum p
  rcases (by omega : pairs (sumCls p) = 1 ∧ pairs (difCls p) = 2 ∨
      pairs (sumCls p) = 2 ∧ pairs (difCls p) = 1) with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · exact one_two hq h5 hn _ _ h1 h2 hS hD hsq
  · exact one_two hq h5 hn _ _ h1 h2 hD hS (by linear_combination hsq)

/-- **Theorem `thm:levels`** (all three parts). -/
theorem levels (p : Equiv.Perm (Fin n)) :
    conf p ≠ 1 ∧ (n.Prime → 5 ≤ n → conf p ≠ 2) ∧
      ∀ q : ℕ, q.Prime → 5 ≤ q → n = 2 * q → conf p ≠ 3 :=
  ⟨conf_ne_one p, conf_ne_two_prime p, fun _ hq h5 hn => conf_ne_three p hq h5 hn⟩

end Levels

#print axioms Levels.levels
