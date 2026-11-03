import Mathlib

/-!
# No permutation has exactly one toroidal conflict

Lean pilot (2026-10-18) for the floor theorem of "The fewest and the most toroidal conflicts" (Proposition
`prop:lower`, first part). A permutation `p` of `Fin n` places one queen per row and column. Its wrapped sum class
of row `i` is `i + p i` and its wrapped difference class is `i - p i`, both in `ZMod n`. A conflict is a pair of rows
sharing a class; conflicts are counted per family. The paper's argument uses only sums of classes, so the statement
holds for every permutation, not only for solutions.
-/

open Finset

namespace Queens

variable {n : ℕ} [NeZero n]

/-- Number of pairs of rows `i < j` with the same class under `f`. -/
def pairs (f : Fin n → ZMod n) : ℕ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ f q.1 = f q.2)).card

/-- Wrapped sum class of row `i`. -/
def sumCls (p : Equiv.Perm (Fin n)) (i : Fin n) : ZMod n := ((i : ℕ) : ZMod n) + ((p i : ℕ) : ZMod n)

/-- Wrapped difference class of row `i`. -/
def difCls (p : Equiv.Perm (Fin n)) (i : Fin n) : ZMod n := ((i : ℕ) : ZMod n) - ((p i : ℕ) : ZMod n)

/-- Toroidal conflicts of `p`, counted per family. -/
def conf (p : Equiv.Perm (Fin n)) : ℕ := pairs (sumCls p) + pairs (difCls p)

/-- The sum of all row numbers, read in `ZMod n`. -/
def T (n : ℕ) [NeZero n] : ZMod n := ∑ i : Fin n, ((i : ℕ) : ZMod n)

/-- Row sums of the two families. -/
theorem sum_sumCls (p : Equiv.Perm (Fin n)) : ∑ i, sumCls p i = 2 * T n := by
  have h := Equiv.sum_comp p (fun j : Fin n => ((j : ℕ) : ZMod n))
  unfold sumCls T
  rw [Finset.sum_add_distrib, h, two_mul]

omit [NeZero n] in
theorem sum_difCls (p : Equiv.Perm (Fin n)) : ∑ i, difCls p i = 0 := by
  have h := Equiv.sum_comp p (fun j : Fin n => ((j : ℕ) : ZMod n))
  unfold difCls
  rw [Finset.sum_sub_distrib, h, sub_self]

theorem T_cast : T n = ((∑ i ∈ range n, i : ℕ) : ZMod n) := by
  unfold T
  rw [Fin.sum_univ_eq_sum_range (Nat.cast : ℕ → ZMod n) n, Nat.cast_sum]

/-- `T n = 0` for odd `n`; for even `n`, `T n ≠ 0` but `2 * T n = 0`. -/
theorem T_odd (h : n % 2 = 1) : T n = 0 := by
  rw [T_cast, Finset.sum_range_id]
  have hd : 2 ∣ n - 1 := by omega
  rw [Nat.mul_div_assoc n hd, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem T_even (h : n % 2 = 0) : T n ≠ 0 := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  have hk0 : 0 < k := by omega
  rw [T_cast, Finset.sum_range_id]
  have e : n * (n - 1) / 2 = k * (n - 1) := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  rw [e]
  intro h0
  rw [CharP.cast_eq_zero_iff (ZMod n) n] at h0
  obtain ⟨q, hq⟩ := h0
  have : n - 1 = 2 * q := by
    apply Nat.eq_of_mul_eq_mul_left hk0
    rw [hq, hk]; ring
  omega

theorem two_T : 2 * T n = 0 := by
  rw [T_cast]
  have h2 : (((∑ i ∈ range n, i) * 2 : ℕ) : ZMod n) = 0 := by
    rw [Finset.sum_range_id_mul_two, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  push_cast at h2 ⊢
  linear_combination h2

theorem sum_of_injective (f : Fin n → ZMod n) (hf : Function.Injective f) :
    ∑ i, f i = ∑ r : ZMod n, r := by
  have hb : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by simp [ZMod.card]⟩
  exact hb.sum_comp (fun r => r)

theorem T_eq_sum : T n = ∑ r : ZMod n, r := by
  unfold T
  apply sum_of_injective
  intro i j hij
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at hij
  rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij

omit [NeZero n] in
theorem inj_of_pairs_zero (f : Fin n → ZMod n) (h : pairs f = 0) : Function.Injective f := by
  intro i j hij
  by_contra hne
  unfold pairs at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h (mem_univ (i, j)) ⟨hlt, hij⟩
  · exact h (mem_univ (j, i)) ⟨hlt, hij.symm⟩

/-- An injective class map hits every class once, so its sum is `T n`. -/
theorem sum_of_pairs_zero (f : Fin n → ZMod n) (h : pairs f = 0) : ∑ i, f i = T n := by
  rw [sum_of_injective f (inj_of_pairs_zero f h), T_eq_sum]

/-- One colliding pair: one class doubled (`a`), one missing (`m`). -/
theorem sum_of_pairs_one (f : Fin n → ZMod n) (h : pairs f = 1) :
    ∃ a m : ZMod n, a ≠ m ∧ ∑ i, f i = T n + a - m := by
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
  have hg : ∑ x, g x = T n := by rw [sum_of_injective g hginj, T_eq_sum]
  have e1 := Finset.sum_update_of_mem (mem_univ j) f m
  rw [Finset.sdiff_singleton_eq_erase] at e1
  have e2 := Finset.add_sum_erase univ f (mem_univ j)
  refine ⟨f j, m, hm j, ?_⟩
  rw [hgdef] at hg
  linear_combination -e2 - e1 + hg

/-- No permutation has exactly one toroidal conflict. -/
theorem conf_ne_one (p : Equiv.Perm (Fin n)) : conf p ≠ 1 := by
  intro hc
  unfold conf at hc
  have hs := sum_sumCls p
  have hd := sum_difCls p
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h0 : pairs (sumCls p) = 0 ∨ pairs (difCls p) = 0 := by omega
    rcases h0 with h0 | h0
    · have := sum_of_pairs_zero _ h0
      rw [hs, two_T] at this
      exact T_even he this.symm
    · have := sum_of_pairs_zero _ h0
      rw [hd] at this
      exact T_even he this.symm
  · have hT := T_odd ho
    have h1 : pairs (sumCls p) = 1 ∨ pairs (difCls p) = 1 := by omega
    rcases h1 with h1 | h1
    · obtain ⟨a, m, ham, hsum⟩ := sum_of_pairs_one _ h1
      rw [hs, hT] at hsum
      apply ham
      have : a - m = 0 := by
        rw [mul_zero, zero_add] at hsum; exact hsum.symm
      exact sub_eq_zero.mp this
    · obtain ⟨a, m, ham, hsum⟩ := sum_of_pairs_one _ h1
      rw [hd, hT] at hsum
      apply ham
      have : a - m = 0 := by
        rw [zero_add] at hsum; exact hsum.symm
      exact sub_eq_zero.mp this

end Queens

#print axioms Queens.conf_ne_one
