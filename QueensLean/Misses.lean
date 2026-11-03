import QueensLean.BoardCheck

/-!
# Exhaustive search: the misses

Lean target (2026-10-18) for the exact values at `n = 10, 13, 18` of Corollary `cor:exact`, where the largest number
of conflicts is one below `⌊n/φ⌋`. `go n k f L` extends a partial board `L` (columns of the first rows) row by row
through every safe column and checks at each full board that its toroidal conflicts are at most `k`. `go_sound`:
if `go n k n [] = true`, every `n`-queens solution has at most `k` conflicts. The search is run by `decide +kernel`.
-/

open Finset

namespace Misses

open Queens Ceiling Boards

/-- Placing a queen at row `r`, column `c` attacks none of the queens `L` (rows `i, i+1, …`). -/
def safeAux (r c : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, x :: xs => (x != c) && (i + x != r + c) && (i + c != r + x) && safeAux r c (i + 1) xs

/-- Column `c` is safe for the next row after the partial board `L`. -/
def safe (L : List ℕ) (c : ℕ) : Bool := safeAux L.length c 0 L

/-- Toroidal conflicts of a full board given as a list. -/
def confL (n : ℕ) (L : List ℕ) : ℕ :=
  pairsL (List.ofFn fun i : Fin n => ((i : ℕ) + colsF n L i) % n) +
    pairsL (List.ofFn fun i : Fin n => ((i : ℕ) + n - colsF n L i) % n)

/-- The search: `f` rows still to place. -/
def go (n k : ℕ) : ℕ → List ℕ → Bool
  | 0, L => decide (confL n L ≤ k)
  | f + 1, L => (List.range n).all (fun c => !safe L c || go n k f (L ++ [c]))

theorem safeAux_of (r c : ℕ) : ∀ (i : ℕ) (L : List ℕ),
    (∀ t (h : t < L.length), L[t] ≠ c ∧ i + t + L[t] ≠ r + c ∧ i + t + c ≠ r + L[t]) →
      safeAux r c i L = true
  | _, [], _ => rfl
  | i, x :: xs, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    have ih := safeAux_of r c (i + 1) xs (fun t ht => by
      have := h (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      refine ⟨this.1, by omega, by omega⟩)
    simp [safeAux, h0.1, h0.2.1, h0.2.2, ih]

theorem conf_eq_confL {n : ℕ} [NeZero n] (p : Equiv.Perm (Fin n)) (L : List ℕ)
    (hp : ∀ i, ((p i : Fin n) : ℕ) = colsF n L i) : conf p = confL n L := by
  have hs : ∀ i, sumCls p i = (((i : ℕ) + colsF n L i : ℕ) : ZMod n) := by
    intro i; unfold sumCls; rw [hp]; push_cast; ring
  have hd : ∀ i, difCls p i = (((i : ℕ) + n - colsF n L i : ℕ) : ZMod n) := by
    intro i
    have := hp i ▸ (p i).isLt
    unfold difCls; rw [hp, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]; ring
  unfold conf confL
  rw [pairs_eq (sumCls p) (fun i : Fin n => ((i : ℕ) + colsF n L i) % n)
      (fun i j => by rw [hs, hs, ZMod.natCast_eq_natCast_iff']),
    pairs_eq (difCls p) (fun i : Fin n => ((i : ℕ) + n - colsF n L i) % n)
      (fun i j => by rw [hd, hd, ZMod.natCast_eq_natCast_iff'])]

/-- **Soundness of the search**: every solution has at most `k` conflicts. -/
theorem go_sound {n k : ℕ} [NeZero n] (h : go n k n [] = true) (p : Equiv.Perm (Fin n))
    (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) : conf p ≤ k := by
  set Lp : List ℕ := List.ofFn fun i : Fin n => ((p i : Fin n) : ℕ) with hLp
  have hlen : Lp.length = n := by simp [hLp]
  have hget : ∀ t (ht : t < Lp.length), Lp[t] = ((p ⟨t, hlen ▸ ht⟩ : Fin n) : ℕ) := by
    intro t ht; simp [hLp]
  have hcol : ∀ i : Fin n, ((p i : Fin n) : ℕ) = colsF n Lp i := by
    intro i
    unfold colsF
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact i.isLt)]
    simp [hget]
  -- invariant: a prefix of `Lp` with `f` rows to go
  have key : ∀ f (L : List ℕ), L.length + f = n → L = Lp.take L.length → go n k f L = true →
      confL n Lp ≤ k := by
    intro f
    induction f with
    | zero =>
      intro L hl hL hg
      have hl' : L.length = Lp.length := by omega
      have : L = Lp := calc
        L = Lp.take L.length := hL
        _ = Lp := by rw [hl', List.take_length]
      subst this
      simpa [go] using hg
    | succ f ih =>
      intro L hl hL hg
      set m := L.length with hm
      have hmn : m < Lp.length := by omega
      have hpre : ∀ t (ht : t < L.length), L[t] = Lp[t] := by
        intro t ht
        have : L[t] = (Lp.take m)[t]'(by simp; omega) := by simp only [← hL]
        rw [this, List.getElem_take]
      set c := Lp[m] with hc
      have hcm : c = ((p ⟨m, by omega⟩ : Fin n) : ℕ) := hget m hmn
      have hsafe : safe L c = true := by
        unfold safe
        apply safeAux_of
        intro t ht
        rw [zero_add, hpre t ht, hget t (by omega), hcm]
        have ne : (⟨t, by omega⟩ : Fin n) ≠ ⟨m, by omega⟩ := by
          intro e; simp at e; omega
        refine ⟨fun e => ne (p.injective (Fin.ext e)), fun e => ne (hs ?_), fun e => ne (hd ?_)⟩
        · unfold vs; simp only; push_cast; omega
        · unfold vd; simp only; push_cast; omega
      have hcr : c ∈ List.range n := by
        rw [List.mem_range, hcm]; exact (p _).isLt
      have hg' := List.all_eq_true.mp hg c hcr
      rw [hsafe, Bool.not_true, Bool.false_or] at hg'
      refine ih (L ++ [c]) (by simp; omega) ?_ hg'
      rw [List.length_append, List.length_singleton, ← hm, hL, hc, List.take_append_getElem]
  have := key n [] (by simp) (by simp) h
  rw [conf_eq_confL p Lp hcol]
  exact this

/-- Splitting the search by the first two rows. -/
theorem go_two {n k f : ℕ} (h : ∀ c0 c1, c0 < n → c1 < n → safe [] c0 = true → safe [c0] c1 = true →
    go n k f [c0, c1] = true) : go n k (f + 2) [] = true := by
  simp only [go, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  intro c0 h0
  by_cases s0 : safe [] c0 = true
  · right; intro c1 h1
    by_cases s1 : safe ([] ++ [c0]) c1 = true
    · right; exact h c0 c1 h0 h1 s0 s1
    · left; simpa using s1
  · left; simpa using s0

/-- One row deeper at any prefix: `go` holds at `L` if it holds after every safe next column. -/
theorem go_of {n k f : ℕ} {L : List ℕ} (h : ∀ c, c < n → safe L c = true → go n k f (L ++ [c]) = true) :
    go n k (f + 1) L = true := by
  simp only [go, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  intro c hc
  by_cases s : safe L c = true
  · right; exact h c hc s
  · left; simpa using s

end Misses

#print axioms Misses.go_sound

