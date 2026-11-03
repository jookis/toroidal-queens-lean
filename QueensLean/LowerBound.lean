import QueensLean.OneConflict

/-!
# The rest of the lower bound

Lean target 6 (2026-10-18) for "The fewest and the most toroidal conflicts", Proposition `prop:lower`, with
`Queens.conf_ne_one` (OneConflict.lean) the first part. For every permutation `p` of `Fin n` (so for every
`n`-queens solution), conflicts counted toroidally per family:

* `polya`: `conf p = 0` only if `gcd(n, 6) = 1` (Pólya's theorem);
* `conf_ne_two`: `conf p ≠ 2` if `6 ∣ n`;
* `lower_bound`: `conf p ≥ 2` unless `gcd(n, 6) = 1`, and `conf p ≥ 3` if `6 ∣ n`.

Tools: complete families sum to `T` with squares summing to `Q = ∑_{i<n} i²`; a family with one colliding pair has
sums `T + a - m` and `Q + a² - m²` (`pairs_one_phi`); `∑ s² + ∑ t² = 4Q`; `2Q ≢ 0 (mod n)` when `3 ∣ n`.
-/

open Finset

namespace Lower

open Queens

variable {n : ℕ} [NeZero n]

theorem sum_inj_phi (f : Fin n → ZMod n) (hf : Function.Injective f) (φ : ZMod n → ZMod n) :
    ∑ i, φ (f i) = ∑ r : ZMod n, φ r := by
  have hb : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by simp [ZMod.card]⟩
  exact hb.sum_comp φ

omit [NeZero n] in
theorem cast_inj : Function.Injective (fun i : Fin n => ((i : ℕ) : ZMod n)) := by
  intro i j hij
  apply Fin.ext
  simp only at hij
  rw [ZMod.natCast_eq_natCast_iff'] at hij
  rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij

/-- `Q = ∑_{i<n} i²`. -/
def Q (n : ℕ) : ℕ := ∑ i ∈ range n, i ^ 2

theorem six_Q (n : ℕ) : 6 * (Q n : ℤ) = n * ((n : ℤ) - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp [Q]
  | succ k ih =>
    unfold Q at ih ⊢
    rw [sum_range_succ]
    push_cast at ih ⊢
    linear_combination ih

omit [NeZero n] in
theorem rows_sq : ∑ i : Fin n, ((i : ℕ) : ZMod n) ^ 2 = ((Q n : ℕ) : ZMod n) := by
  unfold Q
  push_cast
  exact Fin.sum_univ_eq_sum_range (fun i => ((i : ℕ) : ZMod n) ^ 2) n

theorem res_sq : ∑ r : ZMod n, r ^ 2 = ((Q n : ℕ) : ZMod n) := by
  have h := sum_inj_phi _ (cast_inj (n := n)) (fun r => r ^ 2)
  rw [← h, rows_sq]

omit [NeZero n] in
/-- Lemma `sums`, squares: `∑ s² + ∑ t² = 4Q`. -/
theorem sq_sum (p : Equiv.Perm (Fin n)) :
    ∑ i, (sumCls p i) ^ 2 + ∑ i, (difCls p i) ^ 2 = 4 * ((Q n : ℕ) : ZMod n) := by
  have h1 := Equiv.sum_comp p (fun j : Fin n => ((j : ℕ) : ZMod n) ^ 2)
  rw [← sum_add_distrib]
  have e : ∀ i, (sumCls p i) ^ 2 + (difCls p i) ^ 2 =
      2 * ((i : ℕ) : ZMod n) ^ 2 + 2 * ((p i : ℕ) : ZMod n) ^ 2 := by
    intro i; unfold sumCls difCls; ring
  simp_rw [e]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, h1, rows_sq]
  ring

/-- `2Q ≢ 0 (mod n)` when `3 ∣ n`. -/
theorem two_Q_ne (h3 : 3 ∣ n) : 2 * ((Q n : ℕ) : ZMod n) ≠ 0 := by
  intro h
  have h' : ((2 * Q n : ℕ) : ZMod n) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  obtain ⟨c, hc⟩ := h'
  obtain ⟨k, hk⟩ := h3
  have hk0 : (k : ℤ) ≠ 0 := by
    have := NeZero.ne n
    intro h0
    have : k = 0 := by exact_mod_cast h0
    omega
  have h6 := six_Q n
  have hcz : 2 * (Q n : ℤ) = n * c := by exact_mod_cast hc
  have hnz : (n : ℤ) = 3 * k := by exact_mod_cast hk
  rw [hnz] at h6 hcz
  have hm : (k : ℤ) * (9 * c - 3 * ((3 * k - 1) * (6 * k - 1))) = 0 := by
    linear_combination h6 - 3 * hcz
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact hk0 h0
  · have : 9 * (c : ℤ) = 3 * (18 * ((k : ℤ) * k) - 9 * k + 1) := by linear_combination h0
    generalize (k : ℤ) * k = K at this
    omega

/-- One colliding pair, for any function `φ` of the class: one class `a` doubled, one class `m` missing. -/
theorem pairs_one_phi (f : Fin n → ZMod n) (h : pairs f = 1) :
    ∃ a m : ZMod n, a ≠ m ∧ ∀ φ : ZMod n → ZMod n, ∑ i, φ (f i) = ∑ r : ZMod n, φ r + φ a - φ m := by
  unfold pairs at h
  obtain ⟨⟨i, j⟩, hq⟩ := Finset.card_eq_one.mp h
  have hmem : (i, j) ∈ (univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ f q.1 = f q.2) := by
    rw [hq]; exact mem_singleton_self _
  obtain ⟨hij, hfij⟩ := (mem_filter.mp hmem).2
  have huniq : ∀ k l : Fin n, k < l → f k = f l → k = i ∧ l = j := by
    intro k l hkl hf
    have : (k, l) ∈ (univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ f q.1 = f q.2) :=
      mem_filter.mpr ⟨mem_univ _, hkl, hf⟩
    rw [hq, mem_singleton, Prod.mk.injEq] at this
    exact this
  obtain ⟨m, hm⟩ : ∃ m : ZMod n, ∀ x, f x ≠ m := by
    by_contra hc
    push Not at hc
    have hb : Function.Bijective f := by
      rw [Fintype.bijective_iff_surjective_and_card]
      exact ⟨hc, by simp [ZMod.card]⟩
    exact absurd (hb.1 hfij) (ne_of_lt hij)
  set g := Function.update f j m with hgdef
  have hginj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    by_cases hx : x = j
    · subst hx
      have hy : y ≠ x := fun e => hne e.symm
      simp only [hgdef, Function.update_self, Function.update_of_ne hy] at hxy
      exact hm y hxy.symm
    by_cases hy : y = j
    · subst hy
      simp only [hgdef, Function.update_self, Function.update_of_ne hx] at hxy
      exact hm x hxy
    simp only [hgdef, Function.update_of_ne hx, Function.update_of_ne hy] at hxy
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hy (huniq x y hlt hxy).2
    · exact hx (huniq y x hlt hxy.symm).2
  refine ⟨f j, m, hm j, fun φ => ?_⟩
  have hg := sum_inj_phi g hginj φ
  have e0 : (fun x => φ (g x)) = Function.update (fun x => φ (f x)) j (φ m) := by
    ext x
    by_cases hx : x = j
    · subst hx; simp [hgdef]
    · simp [hgdef, Function.update_of_ne hx]
  have e1 := Finset.sum_update_of_mem (mem_univ j) (fun x => φ (f x)) (φ m)
  rw [Finset.sdiff_singleton_eq_erase] at e1
  have e2 := Finset.add_sum_erase univ (fun x => φ (f x)) (mem_univ j)
  have e3 : ∑ x, φ (g x) = ∑ x, Function.update (fun x => φ (f x)) j (φ m) x := by rw [← e0]
  linear_combination -e2 - e1 + hg - e3

theorem complete_family {f : Fin n → ZMod n} (h : pairs f = 0) (φ : ZMod n → ZMod n) :
    ∑ i, φ (f i) = ∑ r : ZMod n, φ r :=
  sum_inj_phi f (inj_of_pairs_zero f h) φ

/-- For even `n` neither family can be conflict-free. -/
theorem even_no_free (p : Equiv.Perm (Fin n)) (he : n % 2 = 0) :
    pairs (sumCls p) ≠ 0 ∧ pairs (difCls p) ≠ 0 := by
  constructor
  · intro h0
    have := sum_of_pairs_zero _ h0
    rw [sum_sumCls, two_T] at this
    exact T_even he this.symm
  · intro h0
    have := sum_of_pairs_zero _ h0
    rw [sum_difCls] at this
    exact T_even he this.symm

/-- **Pólya**: a permutation with no toroidal conflict exists only for `gcd(n, 6) = 1`. -/
theorem polya (p : Equiv.Perm (Fin n)) (h : conf p = 0) : Nat.Coprime n 6 := by
  unfold conf at h
  have hs0 : pairs (sumCls p) = 0 := by omega
  have hd0 : pairs (difCls p) = 0 := by omega
  have h2 : ¬ 2 ∣ n := by
    intro h2
    exact (even_no_free p (Nat.mod_eq_zero_of_dvd h2)).1 hs0
  have h3 : ¬ 3 ∣ n := by
    intro h3
    have a1 := complete_family hs0 (fun r => r ^ 2)
    have a2 := complete_family hd0 (fun r => r ^ 2)
    have hsq := sq_sum p
    rw [a1, a2, res_sq] at hsq
    exact two_Q_ne h3 (by linear_combination -hsq)
  rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.coprime_mul_iff_right]
  exact ⟨(Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr h2)),
    (Nat.coprime_comm.mp ((Nat.prime_three.coprime_iff_not_dvd).mpr h3))⟩

/-- **No two conflicts when `6 ∣ n`.** -/
theorem conf_ne_two (p : Equiv.Perm (Fin n)) (h6 : 6 ∣ n) : conf p ≠ 2 := by
  intro hc
  unfold conf at hc
  have he : n % 2 = 0 := by omega
  obtain ⟨hs, hd⟩ := even_no_free p he
  have hs1 : pairs (sumCls p) = 1 := by omega
  have hd1 : pairs (difCls p) = 1 := by omega
  obtain ⟨a, m, -, ha⟩ := pairs_one_phi _ hs1
  obtain ⟨a', m', -, hb⟩ := pairs_one_phi _ hd1
  have hA := ha id
  have hB := hb id
  have hA2 := ha (fun r => r ^ 2)
  have hB2 := hb (fun r => r ^ 2)
  simp only [id] at hA hB hA2 hB2
  rw [sum_sumCls, two_T, ← T_eq_sum] at hA
  rw [sum_difCls, ← T_eq_sum] at hB
  have hsq := sq_sum p
  rw [hA2, hB2, res_sq] at hsq
  have h2T : 2 * T n = 0 := two_T
  apply two_Q_ne (n := n) (by omega)
  linear_combination (-1) * hsq - (a + m - T n) * hA - (a' + m' - T n) * hB - (m + m' - T n) * h2T

/-- **Proposition `prop:lower`** (all three parts together): at least `2` toroidal conflicts unless
`gcd(n, 6) = 1`, and at least `3` when `6 ∣ n`. -/
theorem lower_bound (p : Equiv.Perm (Fin n)) :
    (¬ Nat.Coprime n 6 → 2 ≤ conf p) ∧ (6 ∣ n → 3 ≤ conf p) := by
  have h1 := conf_ne_one p
  constructor
  · intro hc
    by_contra h
    have h0 : conf p = 0 := by omega
    exact hc (polya p h0)
  · intro h6
    have h2 := conf_ne_two p h6
    by_contra h
    have h0 : conf p = 0 := by omega
    have := polya p h0
    rw [Nat.coprime_comm] at this
    have h6' : 6 ∣ Nat.gcd 6 n := Nat.dvd_gcd dvd_rfl h6
    rw [this] at h6'
    omega

end Lower

#print axioms Lower.polya
#print axioms Lower.conf_ne_two
#print axioms Lower.lower_bound
