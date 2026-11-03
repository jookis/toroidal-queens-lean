import QueensLean.Levels

/-!
# The hidden crystal layer

Lean target (2026-10-18) for Theorem `thm:layer` of "The fewest and the most toroidal conflicts". Let `p` be a
permutation with `conf p = f(n)` (the floor: `0` if `gcd(n, 6) = 1`, `3` if `6 ∣ n`, `2` otherwise).

* `layer`: for every prime `K ≥ 5` dividing `n`, each residue modulo `K` holds exactly `n / K` sum classes and
  exactly `n / K` difference classes;
* `layer_even`: if `n` is even and `3 ∤ n`, the same holds for every odd `K ∣ n`.

Tools: the excess `e f r = cnt f r - 1` of `Levels` has a fixed shape for one or two colliding pairs (`shape1`,
`shape2`); a family is balanced modulo `K` as soon as the excess sums to `0` on every residue class (`bal_of_W`).
-/

open Finset

namespace Layer

open Queens Lower Levels

variable {n : ℕ} [NeZero n]

/-- The floor `f(n)`. -/
def floorVal (n : ℕ) : ℕ := if Nat.Coprime n 6 then 0 else if 6 ∣ n then 3 else 2

/-- Indicator as an integer. -/
abbrev ind (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

/-- Balanced modulo `K`: every residue modulo `K` holds exactly `n / K` classes of `f`. -/
def bal (f : Fin n → ZMod n) {K : ℕ} (hK : K ∣ n) : Prop :=
  ∀ ρ : ZMod K, (univ.filter (fun i => ZMod.castHom hK (ZMod K) (f i) = ρ)).card = n / K

theorem sum_e_phi {R : Type*} [CommRing R] (f : Fin n → ZMod n) (φ : ZMod n → R) :
    ∑ i, φ (f i) = ∑ r, φ r + ∑ r, (e f r : R) * φ r := by
  rw [sum_cnt f φ, ← sum_add_distrib]
  refine sum_congr rfl (fun r _ => ?_)
  unfold e; rw [nsmul_eq_mul]; push_cast; ring

theorem shape0 (f : Fin n → ZMod n) (h : pairs f = 0) (r : ZMod n) : e f r = 0 := by
  have hq := sum_e_sq f
  rw [h] at hq
  simp only [Nat.cast_zero, mul_zero] at hq
  exact pow_eq_zero_iff two_ne_zero |>.mp
    ((sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (e f i))).mp hq r (mem_univ r))

/-- Values `-1, 0, 1` once the excess has sum of squares at most `4` and no entry `2`. -/
theorem vals {α : Type*} [Fintype α] [DecidableEq α] (e : α → ℤ) (hl : ∀ r, -1 ≤ e r)
    (hs : ∑ r, e r = 0) (hq : ∑ r, e r ^ 2 ≤ 4) : ∀ r, e r = -1 ∨ e r = 0 ∨ e r = 1 := by
  have hle : ∀ r, e r ^ 2 ≤ 4 := fun r =>
    le_trans (single_le_sum (f := fun i => e i ^ 2) (fun i _ => sq_nonneg (e i)) (mem_univ r)) hq
  have hne2 : ∀ r, e r ≠ 2 := by
    intro r hr
    have h1 := add_sum_erase univ (fun x => e x ^ 2) (mem_univ r)
    have h2 := add_sum_erase univ e (mem_univ r)
    rw [hr] at h1 h2
    have h0 : ∀ x ∈ univ.erase r, e x ^ 2 = 0 := by
      have : ∑ x ∈ univ.erase r, e x ^ 2 = 0 :=
        le_antisymm (by linarith) (sum_nonneg (fun i _ => sq_nonneg (e i)))
      exact (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (e i))).mp this
    have : ∑ x ∈ univ.erase r, e x = 0 :=
      sum_eq_zero (fun x hx => pow_eq_zero_iff two_ne_zero |>.mp (h0 x hx))
    linarith
  intro r
  have := hl r; have := hle r; have := hne2 r
  have : e r ≤ 2 := by nlinarith
  omega

/-- Cards of the `+1` and `-1` sets. -/
theorem cards {α : Type*} [Fintype α] [DecidableEq α] (e : α → ℤ) (h3 : ∀ r, e r = -1 ∨ e r = 0 ∨ e r = 1)
    (hs : ∑ r, e r = 0) (k : ℕ) (hq : ∑ r, e r ^ 2 = 2 * k) :
    (univ.filter (fun r => e r = 1)).card = k ∧ (univ.filter (fun r => e r = -1)).card = k := by
  have hs' : ∑ r, e r = ∑ r, ((if e r = 1 then (1 : ℤ) else 0) - (if e r = -1 then 1 else 0)) :=
    sum_congr rfl (fun r _ => by rcases h3 r with h | h | h <;> simp [h])
  have hq' : ∑ r, e r ^ 2 = ∑ r, ((if e r = 1 then (1 : ℤ) else 0) + (if e r = -1 then 1 else 0)) :=
    sum_congr rfl (fun r _ => by rcases h3 r with h | h | h <;> simp [h])
  rw [sum_sub_distrib, sum_boole, sum_boole] at hs'
  rw [sum_add_distrib, sum_boole, sum_boole] at hq'
  constructor
  · have : ((univ.filter (fun r => e r = 1)).card : ℤ) = k := by linarith
    exact_mod_cast this
  · have : ((univ.filter (fun r => e r = -1)).card : ℤ) = k := by linarith
    exact_mod_cast this

theorem ind_or {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) (r : α) :
    ind (r = a ∨ r = b) = ind (r = a) + ind (r = b) := by
  by_cases ha : r = a
  · subst ha; simp [hab]
  · simp [ha]

/-- Shape of one colliding pair: `+1` at `a`, `-1` at `m`. -/
theorem shape1 (f : Fin n → ZMod n) (h : pairs f = 1) :
    ∃ a m : ZMod n, a ≠ m ∧ ∀ r, e f r = ind (r = a) - ind (r = m) := by
  have hq := sum_e_sq f
  rw [h] at hq
  have h3 := vals (e f) (e_ge f) (sum_e f) (by norm_num [hq])
  obtain ⟨hA, hM⟩ := cards (e f) h3 (sum_e f) 1 (by norm_num [hq])
  obtain ⟨a, hAe⟩ := card_eq_one.mp hA
  obtain ⟨m, hMe⟩ := card_eq_one.mp hM
  have hA' : ∀ r, e f r = 1 ↔ r = a := fun r => by
    have := congrArg (r ∈ ·) hAe; simpa using this
  have hM' : ∀ r, e f r = -1 ↔ r = m := fun r => by
    have := congrArg (r ∈ ·) hMe; simpa using this
  have ham : a ≠ m := fun hh => by
    have h1 := (hA' a).mpr rfl; have h2 := (hM' a).mpr hh; omega
  refine ⟨a, m, ham, fun r => ?_⟩
  have key : e f r = (if e f r = 1 then 1 else 0) - (if e f r = -1 then 1 else 0) := by
    rcases h3 r with h | h | h <;> simp [h]
  rw [key]
  simp only [hA' r, hM' r]

/-- Shape of two colliding pairs: `+1` at `a, b`, `-1` at `m₁, m₂`. -/
theorem shape2 (f : Fin n → ZMod n) (h : pairs f = 2) :
    ∃ a b m1 m2 : ZMod n, a ≠ b ∧ m1 ≠ m2 ∧ a ≠ m1 ∧ a ≠ m2 ∧ b ≠ m1 ∧ b ≠ m2 ∧
      ∀ r, e f r = ind (r = a) + ind (r = b) - ind (r = m1) - ind (r = m2) := by
  have hq := sum_e_sq f
  rw [h] at hq
  have h3 := vals (e f) (e_ge f) (sum_e f) (by norm_num [hq])
  obtain ⟨hA, hM⟩ := cards (e f) h3 (sum_e f) 2 (by norm_num [hq])
  obtain ⟨a, b, hab, hAe⟩ := card_eq_two.mp hA
  obtain ⟨m1, m2, hm, hMe⟩ := card_eq_two.mp hM
  have hA' : ∀ r, e f r = 1 ↔ r = a ∨ r = b := fun r => by
    have := congrArg (r ∈ ·) hAe; simpa using this
  have hM' : ∀ r, e f r = -1 ↔ r = m1 ∨ r = m2 := fun r => by
    have := congrArg (r ∈ ·) hMe; simpa using this
  have ne : ∀ x y, (x = a ∨ x = b) → (y = m1 ∨ y = m2) → x ≠ y := fun x y hx hy hxy => by
    have h1 := (hA' x).mpr hx; have h2 := (hM' y).mpr hy; rw [hxy] at h1; omega
  refine ⟨a, b, m1, m2, hab, hm, ne _ _ (Or.inl rfl) (Or.inl rfl), ne _ _ (Or.inl rfl) (Or.inr rfl),
    ne _ _ (Or.inr rfl) (Or.inl rfl), ne _ _ (Or.inr rfl) (Or.inr rfl), fun r => ?_⟩
  have key : e f r = (if e f r = 1 then 1 else 0) - (if e f r = -1 then 1 else 0) := by
    rcases h3 r with h | h | h <;> simp [h]
  rw [key]
  simp only [hA' r, hM' r, ind_or hab, ind_or hm]
  ring

theorem e_sum1 {R : Type*} [CommRing R] {f : Fin n → ZMod n} {a m : ZMod n}
    (hsh : ∀ r, e f r = ind (r = a) - ind (r = m)) (φ : ZMod n → R) :
    ∑ r, (e f r : R) * φ r = φ a - φ m := by
  simp_rw [hsh]
  push_cast
  simp [sub_mul, ite_mul, sum_sub_distrib]

theorem e_sum2 {R : Type*} [CommRing R] {f : Fin n → ZMod n} {a b m1 m2 : ZMod n}
    (hsh : ∀ r, e f r = ind (r = a) + ind (r = b) - ind (r = m1) - ind (r = m2)) (φ : ZMod n → R) :
    ∑ r, (e f r : R) * φ r = φ a + φ b - φ m1 - φ m2 := by
  simp_rw [hsh]
  push_cast
  simp [add_mul, sub_mul, ite_mul, sum_add_distrib, sum_sub_distrib]

section fibers

variable {K : ℕ} [NeZero K] (hK : K ∣ n)

/-- Every residue modulo `K` has exactly `n / K` preimages in `ZMod n`. -/
theorem fiber_card (ρ : ZMod K) :
    (univ.filter (fun x : ZMod n => ZMod.castHom hK (ZMod K) x = ρ)).card = n / K := by
  set ψ := ZMod.castHom hK (ZMod K)
  have hsame : ∀ ρ : ZMod K, (univ.filter (fun x : ZMod n => ψ x = ρ)).card =
      (univ.filter (fun x : ZMod n => ψ x = 0)).card := by
    intro ρ
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective ψ ρ
    refine card_bij (fun x _ => x - y) (fun x hx => ?_) (fun x _ x' _ h => by simpa using h)
      (fun z hz => ⟨z + y, ?_, by simp⟩)
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [map_sub, hx, hy, sub_self]
    · simp only [mem_filter, mem_univ, true_and] at hz ⊢
      rw [map_add, hz, hy, zero_add]
  have htot := card_eq_sum_card_fiberwise (f := fun x : ZMod n => ψ x) (s := univ) (t := univ)
    (fun _ _ => mem_univ _)
  simp_rw [hsame] at htot
  rw [sum_const, card_univ, ZMod.card, smul_eq_mul, card_univ, ZMod.card] at htot
  have hd : n / K = (univ.filter (fun x : ZMod n => ψ x = 0)).card :=
    Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne K)) (htot.trans (mul_comm _ _))
  rw [hsame ρ, hd]

/-- Balanced as soon as the excess sums to `0` on every residue class modulo `K`. -/
theorem bal_of_W (f : Fin n → ZMod n)
    (hW : ∀ ρ : ZMod K, ∑ r, (e f r) * ind (ZMod.castHom hK (ZMod K) r = ρ) = 0) : bal f hK := by
  intro ρ
  have h := sum_e_phi f (fun r => ind (ZMod.castHom hK (ZMod K) r = ρ))
  simp only [Int.cast_id] at h
  rw [hW ρ, add_zero, sum_boole, sum_boole, fiber_card hK ρ] at h
  exact_mod_cast h

theorem bal1 (f : Fin n → ZMod n) {a m : ZMod n} (hsh : ∀ r, e f r = ind (r = a) - ind (r = m))
    (h : ZMod.castHom hK (ZMod K) a = ZMod.castHom hK (ZMod K) m) : bal f hK :=
  bal_of_W hK f (fun ρ => by
    have := e_sum1 (R := ℤ) hsh (fun r => ind (ZMod.castHom hK (ZMod K) r = ρ))
    simp only [Int.cast_id] at this
    rw [this, h, sub_self])

theorem bal2 (f : Fin n → ZMod n) {a b m1 m2 : ZMod n}
    (hsh : ∀ r, e f r = ind (r = a) + ind (r = b) - ind (r = m1) - ind (r = m2))
    (h : (ZMod.castHom hK (ZMod K) a = ZMod.castHom hK (ZMod K) m1 ∧
        ZMod.castHom hK (ZMod K) b = ZMod.castHom hK (ZMod K) m2) ∨
      (ZMod.castHom hK (ZMod K) a = ZMod.castHom hK (ZMod K) m2 ∧
        ZMod.castHom hK (ZMod K) b = ZMod.castHom hK (ZMod K) m1)) : bal f hK :=
  bal_of_W hK f (fun ρ => by
    have := e_sum2 (R := ℤ) hsh (fun r => ind (ZMod.castHom hK (ZMod K) r = ρ))
    simp only [Int.cast_id] at this
    rw [this]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring)

theorem bal0 (f : Fin n → ZMod n) (h : pairs f = 0) : bal f hK :=
  bal_of_W hK f (fun ρ => by simp [shape0 f h])

end fibers

/-- `T` vanishes modulo an odd `K ∣ n` when `n` is even. -/
theorem T_mod_even {K : ℕ} (hK : K ∣ n) (hodd : K % 2 = 1) (he : n % 2 = 0) :
    ZMod.castHom hK (ZMod K) (T n) = 0 := by
  rw [T_cast, sum_range_id, map_natCast, ZMod.natCast_eq_zero_iff]
  obtain ⟨h, hh⟩ : ∃ h, n = 2 * h := ⟨n / 2, by omega⟩
  have e1 : n * (n - 1) / 2 = h * (n - 1) := by rw [hh, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [e1]
  have : K ∣ h := by
    rw [hh] at hK
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp ((Nat.coprime_two_left).mpr
      (Nat.odd_iff.mpr hodd))) hK)
  exact Dvd.dvd.mul_right this _

/-- A family with one colliding pair and sum `0`, `n` even, `K` odd: balanced modulo `K`. -/
theorem bal_one {K : ℕ} [NeZero K] (hK : K ∣ n) (hodd : K % 2 = 1) (he : n % 2 = 0) (f : Fin n → ZMod n)
    (h1 : pairs f = 1) (hs : ∑ i, f i = 0) : bal f hK := by
  obtain ⟨a, m, -, hsh⟩ := shape1 f h1
  have e1 := sum_e_phi f id
  rw [e_sum1 hsh] at e1
  simp only [id] at e1
  rw [← T_eq_sum, hs] at e1
  refine bal1 hK f hsh ?_
  have := congrArg (ZMod.castHom hK (ZMod K)) e1
  simp only [map_zero, map_sub, map_add, T_mod_even hK hodd he, zero_add] at this
  exact (sub_eq_zero.mp this.symm)

section main

variable {K : ℕ} [NeZero K] (hK : K ∣ n)

/-- A family with at most one colliding pair whose sum vanishes modulo `K` (with `T ≡ 0`): balanced, and its sum
of squares is `Q` modulo `K`. -/
theorem fam_le_one (hT : ZMod.castHom hK (ZMod K) (T n) = 0) (f : Fin n → ZMod n) (h : pairs f ≤ 1)
    (hs : ZMod.castHom hK (ZMod K) (∑ i, f i) = 0) :
    bal f hK ∧ ZMod.castHom hK (ZMod K) (∑ i, f i ^ 2) = ZMod.castHom hK (ZMod K) ((Q n : ℕ) : ZMod n) := by
  rcases (by omega : pairs f = 0 ∨ pairs f = 1) with h0 | h1
  · refine ⟨bal0 hK f h0, ?_⟩
    have := complete_family h0 (fun r => r ^ 2)
    rw [this, res_sq]
  · obtain ⟨a, m, -, hsh⟩ := shape1 f h1
    have e1 := sum_e_phi f id
    rw [e_sum1 hsh] at e1
    simp only [id] at e1
    rw [← T_eq_sum] at e1
    have e2 := sum_e_phi f (fun r => r ^ 2)
    rw [e_sum1 hsh, res_sq] at e2
    have hψ : ZMod.castHom hK (ZMod K) a = ZMod.castHom hK (ZMod K) m := by
      have := congrArg (ZMod.castHom hK (ZMod K)) e1
      rw [hs] at this
      simp only [map_add, map_sub, hT, zero_add] at this
      exact sub_eq_zero.mp this.symm
    refine ⟨bal1 hK f hsh hψ, ?_⟩
    rw [e2]
    simp only [map_add, map_sub, map_pow, hψ]
    ring

/-- A family with two colliding pairs whose sum and sum of squares match the complete family modulo a prime
`K ≥ 5`: balanced. -/
theorem fam_two (hKp : K.Prime) (h5 : 5 ≤ K) (hT : ZMod.castHom hK (ZMod K) (T n) = 0) (f : Fin n → ZMod n)
    (h2 : pairs f = 2) (hs : ZMod.castHom hK (ZMod K) (∑ i, f i) = 0)
    (hq : ZMod.castHom hK (ZMod K) (∑ i, f i ^ 2) = ZMod.castHom hK (ZMod K) ((Q n : ℕ) : ZMod n)) :
    bal f hK := by
  have := Fact.mk hKp
  have h2K : (2 : ZMod K) ≠ 0 := by exact_mod_cast natCast_ne (m := K) (k := 2) (by norm_num) (by omega)
  obtain ⟨a, b, m1, m2, -, -, -, -, -, -, hsh⟩ := shape2 f h2
  have e1 := sum_e_phi f id
  rw [e_sum2 hsh] at e1
  simp only [id] at e1
  rw [← T_eq_sum] at e1
  have e2 := sum_e_phi f (fun r => r ^ 2)
  rw [e_sum2 hsh, res_sq] at e2
  have m1' := congrArg (ZMod.castHom hK (ZMod K)) e1
  have m2' := congrArg (ZMod.castHom hK (ZMod K)) e2
  rw [hs] at m1'
  rw [hq] at m2'
  simp only [map_add, map_sub, map_pow, hT, zero_add] at m1' m2'
  have hs' : ZMod.castHom hK (ZMod K) a + ZMod.castHom hK (ZMod K) b =
      ZMod.castHom hK (ZMod K) m1 + ZMod.castHom hK (ZMod K) m2 := by linear_combination -m1'
  have hq' : ZMod.castHom hK (ZMod K) a ^ 2 + ZMod.castHom hK (ZMod K) b ^ 2 =
      ZMod.castHom hK (ZMod K) m1 ^ 2 + ZMod.castHom hK (ZMod K) m2 ^ 2 := by linear_combination -m2'
  refine bal2 hK f hsh ?_
  rcases quad h2K hs' hq' with h | h
  · exact Or.inl ⟨h, by linear_combination hs' - h⟩
  · exact Or.inr ⟨h, by linear_combination hs' - h⟩

end main

/-- **Theorem `thm:layer`**: at the floor, balanced modulo every prime `K ≥ 5` dividing `n`. -/
theorem layer (p : Equiv.Perm (Fin n)) (hc : conf p = floorVal n) {K : ℕ} (hKp : K.Prime) (h5 : 5 ≤ K)
    (hK : K ∣ n) : bal (sumCls p) hK ∧ bal (difCls p) hK := by
  have : NeZero K := ⟨hKp.ne_zero⟩
  have := Fact.mk hKp
  have hodd : K % 2 = 1 := Nat.odd_iff.mp (hKp.odd_of_ne_two (by omega))
  have hT : ZMod.castHom hK (ZMod K) (T n) = 0 := by
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · exact T_mod_even hK hodd he
    · rw [T_odd ho, map_zero]
  have hQ : ZMod.castHom hK (ZMod K) ((Q n : ℕ) : ZMod n) = 0 := by
    have h2K : (2 : ZMod K) ≠ 0 := by exact_mod_cast natCast_ne (m := K) (k := 2) (by norm_num) (by omega)
    rw [map_natCast]
    rcases mul_eq_zero.mp (two_Q_zero hKp h5 hK) with h | h
    · exact absurd h h2K
    · exact h
  have hS : ZMod.castHom hK (ZMod K) (∑ i, sumCls p i) = 0 := by rw [sum_sumCls, two_T, map_zero]
  have hD : ZMod.castHom hK (ZMod K) (∑ i, difCls p i) = 0 := by rw [sum_difCls, map_zero]
  have hsq := congrArg (ZMod.castHom hK (ZMod K)) (sq_sum p)
  simp only [map_add, map_mul, map_ofNat, hQ, mul_zero] at hsq
  have hle : pairs (sumCls p) ≤ 2 ∧ pairs (difCls p) ≤ 2 := by
    unfold floorVal conf at hc
    split_ifs at hc with h1 h6
    · omega
    · obtain ⟨hs0, hd0⟩ := even_no_free p (by omega)
      omega
    · omega
  unfold conf floorVal at hc
  have h4 : pairs (sumCls p) + pairs (difCls p) ≤ 3 := by split_ifs at hc <;> omega
  rcases (by omega : pairs (sumCls p) ≤ 1 ∨ pairs (sumCls p) = 2 ∧ pairs (difCls p) ≤ 1) with h1 | ⟨h2, h1⟩
  · obtain ⟨b1, q1⟩ := fam_le_one hK hT _ h1 hS
    rcases (by omega : pairs (difCls p) ≤ 1 ∨ pairs (difCls p) = 2) with h1' | h2'
    · exact ⟨b1, (fam_le_one hK hT _ h1' hD).1⟩
    · exact ⟨b1, fam_two hK hKp h5 hT _ h2' hD (by rw [hQ]; linear_combination hsq - q1 - hQ)⟩
  · obtain ⟨b1, q1⟩ := fam_le_one hK hT _ h1 hD
    exact ⟨fam_two hK hKp h5 hT _ h2 hS (by rw [hQ]; linear_combination hsq - q1 - hQ), b1⟩

/-- **Theorem `thm:layer`, second part**: `n` even, `3 ∤ n`, at the floor: balanced modulo every odd `K ∣ n`. -/
theorem layer_even (p : Equiv.Perm (Fin n)) (he : n % 2 = 0) (h3 : ¬ 3 ∣ n) (hc : conf p = floorVal n)
    {K : ℕ} [NeZero K] (hK : K ∣ n) (hodd : K % 2 = 1) : bal (sumCls p) hK ∧ bal (difCls p) hK := by
  have hc2 : conf p = 2 := by
    rw [hc]; unfold floorVal
    have : ¬ Nat.Coprime n 6 := fun h => by
      have := Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) h
      rw [Nat.coprime_two_right] at this
      exact Nat.not_odd_iff_even.mpr (Nat.even_iff.mpr he) this
    have h6 : ¬ 6 ∣ n := fun h6 => h3 (dvd_trans (by norm_num) h6)
    simp [this, h6]
  unfold conf at hc2
  obtain ⟨hs0, hd0⟩ := even_no_free p he
  have hS : ∑ i, sumCls p i = 0 := by rw [sum_sumCls, two_T]
  exact ⟨bal_one hK hodd he _ (by omega) hS, bal_one hK hodd he _ (by omega) (sum_difCls p)⟩

end Layer

#print axioms Layer.layer
#print axioms Layer.layer_even
