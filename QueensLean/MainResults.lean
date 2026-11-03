import QueensLean.OneConflict
import QueensLean.LowerBound
import QueensLean.Levels
import QueensLean.Layer
import QueensLean.NoCycles
import QueensLean.PointSets
import QueensLean.FibSlack
import QueensLean.Ceiling
import QueensLean.Golden
import QueensLean.FloorAll
import QueensLean.Ceilings
import QueensLean.CeilingsRouteA

/-!
# Main results of the paper, in one place

"The fewest and the most toroidal conflicts of an n-queens solution". This file restates every main result with
the definitions it uses; each proof is a single reference to the theorem in its module, so this file is what a reader
compares with the paper. The exhaustive searches for `C(10)` and `C(13)` are in `QueensLeanHeavy/MainResultsHeavy.lean`.

A solution is a permutation `p : Equiv.Perm (Fin n)` (row `i` holds a queen in column `p i`) with
`Function.Injective (vs p)` and `Function.Injective (vd p)` (no two queens on a flat diagonal). Some statements below
hold for every permutation; they then say so by having no such hypothesis.
-/

open Finset Real

namespace MainResults

/-! ## Definitions, unfolded -/

/-- Flat diagonals: `vs p i = i + p i`, `vd p i = i - p i` in the integers. -/
theorem vs_def {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Ceiling.vs p i = (i : ℕ) + ((p i : ℕ) : ℤ) := rfl
theorem vd_def {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Ceiling.vd p i = (i : ℕ) - ((p i : ℕ) : ℤ) := rfl

/-- Wrapped diagonals: the sum and difference classes modulo `n`. -/
theorem sumCls_def {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    Queens.sumCls p i = ((i : ℕ) : ZMod n) + ((p i : ℕ) : ZMod n) := rfl
theorem difCls_def {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    Queens.difCls p i = ((i : ℕ) : ZMod n) - ((p i : ℕ) : ZMod n) := rfl

/-- `pairs f`: the number of rows `i < j` with `f i = f j`. -/
theorem pairs_def {n : ℕ} (f : Fin n → ZMod n) :
    Queens.pairs f = ((univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ f q.1 = f q.2)).card := rfl

/-- Toroidal conflicts `conf p` (the paper's `H(p)`): pairs on a common wrapped diagonal, both families. -/
theorem conf_def {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Queens.conf p = Queens.pairs (Queens.sumCls p) + Queens.pairs (Queens.difCls p) := rfl

/-- The floor `f(n)`: 0, 2 or 3, according as neither, exactly one, or both of 2 and 3 divide `n`. -/
theorem floorVal_def (n : ℕ) : Layer.floorVal n = if Nat.Coprime n 6 then 0 else if 6 ∣ n then 3 else 2 := rfl

/-- The row sum of the golden proof: `S(n) = 2 ∑_{r < n} g(ρ_r)`. -/
theorem S_def (n : ℕ) : FibSlack.S n = 2 * ∑ r ∈ range n, FibSlack.g (FibSlack.ρ n r) := rfl

/-! ## The fewest conflicts -/

/-- **Theorem 2 (floor).** For `n ≠ 2, 3` some solution has exactly `f(n)` conflicts, and every permutation has at
least `f(n)`. -/
theorem floor (n : ℕ) [NeZero n] (h2 : n ≠ 2) (h3 : n ≠ 3) :
    (∃ p : Equiv.Perm (Fin n), Function.Injective (Ceiling.vs p) ∧ Function.Injective (Ceiling.vd p) ∧
      Queens.conf p = Layer.floorVal n) ∧ ∀ p : Equiv.Perm (Fin n), Layer.floorVal n ≤ Queens.conf p :=
  Construct.floor_exact n h2 h3

/-- **Proposition 10 (lower bound)**, for every permutation. -/
theorem lower {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) :
    (¬ Nat.Coprime n 6 → 2 ≤ Queens.conf p) ∧ (6 ∣ n → 3 ≤ Queens.conf p) :=
  Lower.lower_bound p

/-- **Theorem 3 (forbidden levels)**, for every permutation: never 1; never 2 at a prime `n ≥ 5`; never 3 at
`n = 2q` with `q ≥ 5` prime. -/
theorem levels {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) :
    Queens.conf p ≠ 1 ∧ (n.Prime → 5 ≤ n → Queens.conf p ≠ 2) ∧
      ∀ q : ℕ, q.Prime → 5 ≤ q → n = 2 * q → Queens.conf p ≠ 3 :=
  Levels.levels p

/-- **Theorem 4 (hidden crystal layer)**, for every permutation with `f(n)` conflicts: balanced modulo every prime
`K ≥ 5` dividing `n`. -/
theorem layer {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (hc : Queens.conf p = Layer.floorVal n) {K : ℕ}
    (hKp : K.Prime) (h5 : 5 ≤ K) (hK : K ∣ n) :
    Layer.bal (Queens.sumCls p) hK ∧ Layer.bal (Queens.difCls p) hK :=
  Layer.layer p hc hKp h5 hK

/-- **Theorem 4, even case**: for even `n` prime to 3, balanced modulo every odd `K` dividing `n`. -/
theorem layer_even {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (he : n % 2 = 0) (h3 : ¬ 3 ∣ n)
    (hc : Queens.conf p = Layer.floorVal n) {K : ℕ} [NeZero K] (hK : K ∣ n) (hodd : K % 2 = 1) :
    Layer.bal (Queens.sumCls p) hK ∧ Layer.bal (Queens.difCls p) hK :=
  Layer.layer_even p he h3 hc hK hodd

/-! ## No cycles -/

/-- **Theorem 5, first part.** The conflict graph of a solution has no cycle. -/
theorem no_cycles {n : ℕ} {p : Equiv.Perm (Fin n)} (hs : Function.Injective (Ceiling.vs p))
    (hd : Function.Injective (Ceiling.vd p)) : (NoCycles.conflictGraph p).IsAcyclic :=
  NoCycles.acyclic hs hd

/-- **Theorem 5, second part.** No set of squares with at most two on each wrapped diagonal has a cycle of
conflicts. -/
theorem no_cycles_point_sets {n : ℕ} {P : Finset (PointSets.Sq n)} (h2 : PointSets.AtMostTwo P) :
    (PointSets.conflictGraph P).IsAcyclic :=
  PointSets.acyclic h2

/-! ## The most conflicts -/

/-- **Theorem 17 (golden ceiling).** A solution has at most `(√5 - 1) n / 2` conflicts, so at most `⌊n/φ⌋`. -/
theorem golden_ceiling {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (hs : Function.Injective (Ceiling.vs p))
    (hd : Function.Injective (Ceiling.vd p)) :
    (Queens.conf p : ℝ) ≤ (√5 - 1) / 2 * n ∧ (Queens.conf p : ℤ) ≤ ⌊(n : ℝ) / goldenRatio⌋ :=
  Golden.golden_ceiling p hs hd

/-- **Remark 18.** The sharper bound `conf p ≤ S(n)`. -/
theorem conf_le_S {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (hs : Function.Injective (Ceiling.vs p))
    (hd : Function.Injective (Ceiling.vd p)) : (Queens.conf p : ℝ) ≤ FibSlack.S n :=
  Ceiling.conf_le_S p hs hd

/-- **Remark 18.** `C(89) ≤ 54 = ⌊89/φ⌋ - 1`. -/
theorem conf_le_54 (p : Equiv.Perm (Fin 89)) (hs : Function.Injective (Ceiling.vs p))
    (hd : Function.Injective (Ceiling.vd p)) : Queens.conf p ≤ 54 :=
  Ceiling.conf_le_54 p hs hd

/-- **Remark 18, Fibonacci sizes.** At `n = F_m` with `m ≡ 5 (mod 6)` the ceiling is at most `⌊F_m/φ⌋ - 1`. -/
theorem conf_le_fib {m : ℕ} (hm : 5 ≤ m) (h6 : m % 6 = 5) {n : ℕ} [NeZero n] (hn : n = Nat.fib m)
    (p : Equiv.Perm (Fin n)) (hs : Function.Injective (Ceiling.vs p)) (hd : Function.Injective (Ceiling.vd p)) :
    (Queens.conf p : ℤ) ≤ ⌊(Nat.fib m : ℝ) / goldenRatio⌋ - 1 :=
  Ceiling.conf_le_fib hm h6 hn p hs hd

/-- **Remark 18, Fibonacci sizes.** No slack at `m ≡ 1, 3 (mod 6)`. -/
theorem slack_zero {m : ℕ} (hm : 5 ≤ m) (h : m % 6 = 1 ∨ m % 6 = 3) :
    FibSlack.S (Nat.fib m) = ⌊(Nat.fib m : ℝ) / goldenRatio⌋ :=
  FibSlack.slack_zero hm h

/-- **Remark 18, Fibonacci sizes.** `⌊S(F_m)⌋ = ⌊F_m/φ⌋ - 1` at `m ≡ 5 (mod 6)`. -/
theorem floor_S_neg {m : ℕ} (hm : 5 ≤ m) (h : m % 6 = 5) :
    ⌊FibSlack.S (Nat.fib m)⌋ = ⌊(Nat.fib m : ℝ) / goldenRatio⌋ - 1 :=
  FibSlack.floor_S_neg hm h

/-- **Remark 18, Fibonacci sizes.** At even `m ≥ 6`, `S(F_m)` lies strictly between `⌊F_m/φ⌋` and `⌊F_m/φ⌋ + 1`. -/
theorem slack_even {m : ℕ} (hm : 6 ≤ m) (he : Even m) :
    (⌊(Nat.fib m : ℝ) / goldenRatio⌋ : ℝ) < FibSlack.S (Nat.fib m) ∧
      FibSlack.S (Nat.fib m) < ⌊(Nat.fib m : ℝ) / goldenRatio⌋ + 1 :=
  FibSlack.slack_even hm he

/-- **Corollary 19, one size shown** (the 56 sizes of `Ceilings.lean` and the 5 of `CeilingsRouteA.lean` all have this
form: `C(n) = ⌊n/φ⌋`, from a stored board and Theorem 17). -/
theorem C_34 : ⌊(34 : ℝ) / Real.goldenRatio⌋ = 21 ∧
    (∃ p : Equiv.Perm (Fin 34), Function.Injective (Ceiling.vs p) ∧ Function.Injective (Ceiling.vd p) ∧
      Queens.conf p = 21) ∧
    ∀ p : Equiv.Perm (Fin 34), Function.Injective (Ceiling.vs p) → Function.Injective (Ceiling.vd p) →
      Queens.conf p ≤ 21 :=
  Ceilings.C_34

end MainResults
