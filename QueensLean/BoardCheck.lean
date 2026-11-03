import QueensLean.Golden

/-!
# Checking concrete boards

A board is given as a list `L` of columns (row `i` holds its queen in column `L[i]`). `check n k L` is a plain
computation on lists; `sound` proves once and for all that `check n k L = true` gives an `n`-queens solution with
exactly `k` toroidal conflicts. A concrete board is then checked by `decide +kernel` (Lean's kernel evaluates
`check`; no extra axiom). With `Golden.golden_ceiling` this gives exact values of the largest number of conflicts.
-/

open Finset

namespace Boards

open Queens Ceiling

/-- Number of pairs `i < j` with equal entries. -/
def pairsL : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.count x + pairsL xs

theorem count_ofFn {n : ℕ} (g : Fin n → ℕ) (a : ℕ) :
    (List.ofFn g).count a = ∑ j, if g j = a then 1 else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun j => g j.succ), Fin.sum_univ_succ]
    simp only [beq_iff_eq]
    ring

theorem pairsL_ofFn {n : ℕ} (f : Fin n → ℕ) :
    pairsL (List.ofFn f) = ∑ i, ∑ j, if i < j ∧ f i = f j then 1 else 0 := by
  induction n with
  | zero => simp [pairsL]
  | succ k ih =>
    rw [List.ofFn_succ, pairsL, ih (fun i => f i.succ), count_ofFn, Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ, lt_irrefl, false_and, ite_false, zero_add, Fin.succ_pos, true_and,
      Fin.succ_lt_succ_iff, Fin.not_lt_zero]
    congr 1
    refine sum_congr rfl (fun j _ => ?_)
    simp only [eq_comm]

/-- Toroidal pairs of a class map, computed through any map `h` with the same equalities. -/
theorem pairs_eq {n : ℕ} (f : Fin n → ZMod n) (h : Fin n → ℕ) (hf : ∀ i j, f i = f j ↔ h i = h j) :
    pairs f = pairsL (List.ofFn h) := by
  rw [pairsL_ofFn]
  unfold pairs
  rw [card_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
  simp only [hf]

/-- Column of row `i`. -/
def colsF (n : ℕ) (L : List ℕ) (i : Fin n) : ℕ := L.getD i 0

/-- The checker: a permutation, distinct flat sums and differences, and `k` toroidal conflicts. -/
def check (n k : ℕ) (L : List ℕ) : Bool :=
  decide (∀ i : Fin n, colsF n L i < n) &&
  decide (List.ofFn (colsF n L)).Nodup &&
  decide (List.ofFn fun i : Fin n => (i : ℕ) + colsF n L i).Nodup &&
  decide (List.ofFn fun i : Fin n => (i : ℕ) + n - colsF n L i).Nodup &&
  (pairsL (List.ofFn fun i : Fin n => ((i : ℕ) + colsF n L i) % n) +
    pairsL (List.ofFn fun i : Fin n => ((i : ℕ) + n - colsF n L i) % n) == k)

/-- **Soundness** of the checker, keeping the board: `p i` is column `L[i]`. -/
theorem sound_val {n k : ℕ} {L : List ℕ} (h : check n k L = true) :
    ∃ p : Equiv.Perm (Fin n), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧ conf p = k ∧
      ∀ i, ((p i : Fin n) : ℕ) = colsF n L i := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  set g := colsF n L with hg
  let f : Fin n → Fin n := fun i => ⟨g i, h1 i⟩
  have finj : Function.Injective f := by
    intro i j hij
    apply List.nodup_ofFn.mp h2
    exact congrArg Fin.val hij
  have fbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨finj, rfl⟩
  let p := Equiv.ofBijective f fbij
  have hp : ∀ i, ((p i : Fin n) : ℕ) = g i := fun i => rfl
  have hs : ∀ i, sumCls p i = (((i : ℕ) + g i : ℕ) : ZMod n) := by
    intro i; unfold sumCls; rw [hp]; push_cast; ring
  have hd : ∀ i, difCls p i = (((i : ℕ) + n - g i : ℕ) : ZMod n) := by
    intro i
    have := h1 i
    unfold difCls; rw [hp, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]; ring
  refine ⟨p, ?_, ?_, ?_, hp⟩
  · intro i j hij
    unfold vs at hij
    rw [hp, hp] at hij
    apply List.nodup_ofFn.mp h3
    simp only
    omega
  · intro i j hij
    unfold vd at hij
    rw [hp, hp] at hij
    have := h1 i
    have := h1 j
    apply List.nodup_ofFn.mp h4
    simp only
    omega
  · unfold conf
    rw [pairs_eq (sumCls p) (fun i : Fin n => ((i : ℕ) + g i) % n)
        (fun i j => by rw [hs, hs, ZMod.natCast_eq_natCast_iff']),
      pairs_eq (difCls p) (fun i : Fin n => ((i : ℕ) + n - g i) % n)
        (fun i j => by rw [hd, hd, ZMod.natCast_eq_natCast_iff'])]
    exact h5

/-- **Soundness** of the checker. -/
theorem sound {n k : ℕ} {L : List ℕ} (h : check n k L = true) :
    ∃ p : Equiv.Perm (Fin n), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧ conf p = k :=
  let ⟨p, h1, h2, h3, _⟩ := sound_val h; ⟨p, h1, h2, h3⟩

/-- The golden ceiling in natural numbers: if `5n² < (2k + 2 + n)²`, every solution has at most `k` conflicts. -/
theorem conf_le_of {n k : ℕ} [NeZero n] (hk : 5 * n ^ 2 < (2 * k + 2 + n) ^ 2) (p : Equiv.Perm (Fin n))
    (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) : conf p ≤ k := by
  have h := (Golden.golden_ceiling p hs hd).1
  have hk' : (5 : ℝ) * n ^ 2 < (2 * k + 2 + n) ^ 2 := by exact_mod_cast hk
  have hsq : √5 * n < 2 * k + 2 + n := by
    have e : √5 * n = √(5 * n ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    rw [e, Real.sqrt_lt' (by positivity)]; exact hk'
  have : (conf p : ℝ) < k + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- `⌊n/φ⌋ = k` from two inequalities in natural numbers. -/
theorem floor_eq_of {n k : ℕ} (h1 : (2 * k + n) ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < (2 * k + 2 + n) ^ 2) :
    ⌊(n : ℝ) / Real.goldenRatio⌋ = k := by
  rw [Int.floor_eq_iff, Golden.div_gold]
  have e : √5 * n = √(5 * n ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have a1 : (2 * k + n : ℝ) ≤ √5 * n := by
    rw [e, Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast h1
  have a2 : √5 * n < 2 * k + 2 + n := by
    rw [e, Real.sqrt_lt' (by positivity)]; exact_mod_cast h2
  push_cast
  constructor <;> linarith

/-- **Exact ceiling from a board**: a checked board with `k = ⌊n/φ⌋` conflicts gives `C(n) = ⌊n/φ⌋`. -/
theorem ceiling_exact {n k : ℕ} [NeZero n] {L : List ℕ} (hc : check n k L = true)
    (h1 : (2 * k + n) ^ 2 ≤ 5 * n ^ 2) (h2 : 5 * n ^ 2 < (2 * k + 2 + n) ^ 2) :
    ⌊(n : ℝ) / Real.goldenRatio⌋ = k ∧
      (∃ p : Equiv.Perm (Fin n), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧ conf p = k) ∧
      ∀ p : Equiv.Perm (Fin n), Function.Injective (vs p) → Function.Injective (vd p) → conf p ≤ k :=
  ⟨floor_eq_of h1 h2, sound hc, fun p hs hd => conf_le_of h2 p hs hd⟩

/-- Positive control at `n = 8`: a solution with `⌊8/φ⌋ = 4` conflicts. -/
example : check 8 4 [2, 4, 1, 7, 0, 6, 3, 5] = true := by decide +kernel

end Boards

#print axioms Boards.ceiling_exact

/-! Negative controls: the checker rejects a wrong conflict count, a non-solution and a non-permutation. -/
example : Boards.check 8 5 [2, 4, 1, 7, 0, 6, 3, 5] = false := by decide +kernel
example : Boards.check 8 3 [2, 4, 1, 7, 0, 6, 3, 5] = false := by decide +kernel
example : Boards.check 8 4 [0, 4, 7, 5, 2, 6, 1, 3] = false := by decide +kernel
example : Boards.check 8 4 [0, 1, 2, 3, 4, 5, 6, 7] = false := by decide +kernel
example : Boards.check 8 4 [0, 4, 7, 5, 2, 6, 1, 1] = false := by decide +kernel
