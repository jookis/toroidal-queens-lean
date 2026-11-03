import QueensLean.PointSets
import QueensLean.Layer
import QueensLean.Ceiling

/-!
# From a placement to a solution

Lean target (2026-10-18) for the floor constructions of "The fewest and the most toroidal conflicts" (Lemma
`lem:completion`). Queens are indexed by any finite type `ι` with `n` elements; queen `i` stands in column `X i`
and row `Y i`. `build`: if columns and rows are all distinct, flat sums and differences are all distinct, and every
wrapped match of a family (flat values differing by exactly `n`) has exactly one member in a given set (`Bs` for sums,
`Bd` for differences), then there is a solution with at most `|Bs| + |Bd|` toroidal conflicts.
-/

open Finset

namespace Construct

open Queens Ceiling

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Two distinct naturals below `2n` with the same residue modulo `n` differ by exactly `n`. -/
theorem wrap {a b : ℕ} (ha : a < 2 * n) (hb : b < 2 * n) (hab : a ≠ b) (h : (a : ZMod n) = b) :
    a = b + n ∨ b = a + n := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have d : ((n : ℕ) : ℤ) ∣ (b : ℤ) - a := by
    have := Int.ModEq.dvd (show (a : ℤ) ≡ b [ZMOD n] by
      unfold Int.ModEq; exact_mod_cast h)
    exact this
  rcases PointSets.shift (n := n) d (by omega) (by omega) (by omega) with e | e <;> omega

/-- Pairs of a class map sharing a class, bounded by a set meeting every such pair exactly once. -/
theorem pairs_le (f : Fin n → ZMod n) (e : ι ≃ Fin n) (B : Finset ι)
    (hB : ∀ i j, i ≠ j → f (e i) = f (e j) → Xor (i ∈ B) (j ∈ B)) : pairs f ≤ B.card := by
  classical
  unfold pairs
  set S := (univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ f q.1 = f q.2)
  let φ : Fin n × Fin n → ι := fun q => if e.symm q.1 ∈ B then e.symm q.1 else e.symm q.2
  let ψ : Fin n × Fin n → ι := fun q => if e.symm q.1 ∈ B then e.symm q.2 else e.symm q.1
  have key : ∀ q ∈ S, φ q ∈ B ∧ ψ q ∉ B ∧ f (e (φ q)) = f (e (ψ q)) ∧
      ({e.symm q.1, e.symm q.2} : Finset ι) = {φ q, ψ q} := by
    intro q hq
    obtain ⟨hlt, hf⟩ := (mem_filter.mp hq).2
    have hne : e.symm q.1 ≠ e.symm q.2 := fun h => (ne_of_lt hlt) (e.symm.injective h)
    have hx := hB _ _ hne (by simp only [Equiv.apply_symm_apply]; exact hf)
    by_cases h1 : e.symm q.1 ∈ B
    · have h2 : e.symm q.2 ∉ B := by
        rcases hx with ⟨_, h⟩ | ⟨_, h⟩
        · exact h
        · exact absurd h1 h
      simp only [φ, ψ, if_pos h1]
      exact ⟨h1, h2, by simp only [Equiv.apply_symm_apply]; exact hf, trivial⟩
    · have h2 : e.symm q.2 ∈ B := by
        rcases hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h h1
        · exact h
      simp only [φ, ψ, if_neg h1]
      exact ⟨h2, h1, by simp only [Equiv.apply_symm_apply]; exact hf.symm, pair_comm _ _⟩
  apply card_le_card_of_injOn φ (fun q hq => (key q hq).1)
  intro q1 hq1 q2 hq2 heq
  obtain ⟨b1, u1, f1, s1⟩ := key q1 hq1
  obtain ⟨b2, u2, f2, s2⟩ := key q2 hq2
  have hu : ψ q1 = ψ q2 := by
    by_contra hne
    have := hB _ _ hne (by rw [← f1, ← f2, heq])
    rcases this with ⟨h, _⟩ | ⟨h, _⟩
    · exact u1 h
    · exact u2 h
  have hs : ({e.symm q1.1, e.symm q1.2} : Finset ι) = {e.symm q2.1, e.symm q2.2} := by
    rw [s1, s2, heq, hu]
  have l1 := (mem_filter.mp hq1).2.1
  have l2 := (mem_filter.mp hq2).2.1
  have m1 : e.symm q1.1 ∈ ({e.symm q2.1, e.symm q2.2} : Finset ι) := hs ▸ by simp
  have m2 : e.symm q1.2 ∈ ({e.symm q2.1, e.symm q2.2} : Finset ι) := hs ▸ by simp
  simp only [mem_insert, mem_singleton, EmbeddingLike.apply_eq_iff_eq] at m1 m2
  rcases m1 with a | a <;> rcases m2 with b | b
  · rw [a, b] at l1; exact absurd l1 (lt_irrefl _)
  · exact Prod.ext a b
  · rw [a, b] at l1; exact absurd (lt_trans l1 l2) (lt_irrefl _)
  · rw [a, b] at l1; exact absurd l1 (lt_irrefl _)

/-- **From a placement to a solution.** -/
theorem build (X Y : ι → ℕ) (hc : Fintype.card ι = n) (hX : ∀ i, X i < n) (hY : ∀ i, Y i < n)
    (h1 : ∀ i j, i ≠ j → X i ≠ X j ∧ Y i ≠ Y j ∧ X i + Y i ≠ X j + Y j ∧ X i + Y j ≠ X j + Y i)
    (Bs Bd : Finset ι)
    (hs : ∀ i j, i ≠ j → X i + Y i = X j + Y j + n → Xor (i ∈ Bs) (j ∈ Bs))
    (hd : ∀ i j, i ≠ j → Y i + X j = Y j + X i + n → Xor (i ∈ Bd) (j ∈ Bd)) :
    ∃ p : Equiv.Perm (Fin n), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
      conf p ≤ Bs.card + Bd.card := by
  have bij : ∀ Z : ι → ℕ, ∀ hZ : (∀ i, Z i < n), (∀ i j, i ≠ j → Z i ≠ Z j) →
      Function.Bijective (fun i => (⟨Z i, hZ i⟩ : Fin n)) := by
    intro Z hZ hZi
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j h => ?_, by simp [hc]⟩
    by_contra hne
    exact hZi i j hne (congrArg Fin.val h)
  let ey : ι ≃ Fin n := Equiv.ofBijective _ (bij Y hY (fun i j h => (h1 i j h).2.1))
  let ex : ι ≃ Fin n := Equiv.ofBijective _ (bij X hX (fun i j h => (h1 i j h).1))
  let p : Equiv.Perm (Fin n) := ey.symm.trans ex
  have hey : ∀ i, ((ey i : Fin n) : ℕ) = Y i := fun i => rfl
  have hp : ∀ i, ((p (ey i) : Fin n) : ℕ) = X i := by
    intro i; simp only [p, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl
  refine ⟨p, ?_, ?_, ?_⟩
  · intro r r' h
    obtain ⟨i, rfl⟩ := ey.surjective r
    obtain ⟨j, rfl⟩ := ey.surjective r'
    unfold vs at h
    rw [hey, hey, hp, hp] at h
    by_contra hne
    exact (h1 i j (fun e => hne (by rw [e]))).2.2.1 (by omega)
  · intro r r' h
    obtain ⟨i, rfl⟩ := ey.surjective r
    obtain ⟨j, rfl⟩ := ey.surjective r'
    unfold vd at h
    rw [hey, hey, hp, hp] at h
    by_contra hne
    exact (h1 i j (fun e => hne (by rw [e]))).2.2.2 (by omega)
  · unfold conf
    apply add_le_add
    · apply pairs_le _ ey Bs
      intro i j hij heq
      unfold sumCls at heq
      rw [hey, hey, hp, hp] at heq
      have ha := hX i; have hb := hX j; have hc' := hY i; have hd' := hY j
      have := wrap (n := n) (a := Y i + X i) (b := Y j + X j) (by omega) (by omega)
        (by have := (h1 i j hij).2.2.1; omega) (by push_cast; exact heq)
      rcases this with e | e
      · exact hs i j hij (by omega)
      · exact (hs j i (Ne.symm hij) (by omega)).symm
    · apply pairs_le _ ey Bd
      intro i j hij heq
      unfold difCls at heq
      rw [hey, hey, hp, hp] at heq
      have ha := hX i; have hb := hX j; have hc' := hY i; have hd' := hY j
      have e2 : ∀ k, ((Y k : ℕ) : ZMod n) - ((X k : ℕ) : ZMod n) = ((Y k + n - X k : ℕ) : ZMod n) := by
        intro k
        have := hX k
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]; ring
      rw [e2, e2] at heq
      have := wrap (n := n) (a := Y i + n - X i) (b := Y j + n - X j) (by omega) (by omega)
        (by have := (h1 i j hij).2.2.2; omega) heq
      rcases this with e | e
      · exact hd i j hij (by omega)
      · exact (hd j i (Ne.symm hij) (by omega)).symm

end Construct

#print axioms Construct.build

namespace Construct

open Queens Ceiling Layer

/-- `f(n)` from `n mod 6`. -/
theorem floorVal_mod (n : ℕ) :
    Layer.floorVal n = if n % 6 = 1 ∨ n % 6 = 5 then 0 else if n % 6 = 0 then 3 else 2 := by
  unfold Layer.floorVal
  have h6 : (6 ∣ n) ↔ n % 6 = 0 := Nat.dvd_iff_mod_eq_zero
  have hc : Nat.Coprime n 6 ↔ (n % 6 = 1 ∨ n % 6 = 5) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.coprime_mul_iff_right, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.coprime_comm (m := 3),
      Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  by_cases h1 : n % 6 = 1 ∨ n % 6 = 5
  · simp [hc.mpr h1, h1]
  · rw [if_neg (fun h => h1 (hc.mp h)), if_neg h1]
    by_cases h0 : n % 6 = 0
    · simp [h6.mpr h0, h0]
    · rw [if_neg (fun h => h0 (h6.mp h)), if_neg h0]

/-- Every permutation has at least `f(n)` conflicts (Proposition `prop:lower`). -/
theorem floor_le_conf {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) : Layer.floorVal n ≤ conf p := by
  obtain ⟨h1, h2⟩ := Lower.lower_bound p
  unfold Layer.floorVal
  split_ifs with hc h6
  · omega
  · exact h2 h6
  · exact h1 hc

theorem sig_ne {K : ℕ} {L : Fin K → ℕ} {a b : Σ j : Fin K, Fin (L j)} (h : a ≠ b) :
    a.1 ≠ b.1 ∨ (a.2 : ℕ) ≠ b.2 := by
  obtain ⟨j1, k1⟩ := a
  obtain ⟨j2, k2⟩ := b
  by_cases hj : j1 = j2
  · subst hj
    right; intro e; exact h (by congr 1; exact Fin.ext e)
  · left; exact hj

end Construct

namespace Construct

/-- Queens of the runs in `J`, and their number. -/
theorem card_fst {K : ℕ} {L : Fin K → ℕ} (J : Finset (Fin K)) :
    (Finset.univ.filter (fun a : Σ j : Fin K, Fin (L j) => a.1 ∈ J)).card = ∑ j ∈ J, L j := by
  have : Finset.univ.filter (fun a : Σ j : Fin K, Fin (L j) => a.1 ∈ J) = J.sigma fun _ => Finset.univ := by
    ext a; simp
  rw [this, Finset.card_sigma]
  simp

end Construct
