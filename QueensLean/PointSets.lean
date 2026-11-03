import Mathlib

/-!
# No cycles for point sets

Lean target (2026-10-18) for the second part of Theorem `thm:cycles` of "The fewest and the most toroidal
conflicts": no set of squares on the `n × n` board, at most two on each wrapped diagonal, has a cyclic conflict graph
in which every conflict joins the two flat pieces of its wrapped diagonal. Rows and columns play no part, so this
covers Engelhardt's weaker question (a cyclic constellation whose conflicts are all broken by the margins).

A square `q = (r, c)` has flat sum `fs q = r + c` and flat difference `fd q = r - c` (the paper's `t`). A sum
conflict joins two squares with the same wrapped sum `fs % n` but different flat sums (so they lie on the two flat
pieces of one wrapped sum diagonal); a difference conflict likewise. As in the first part, a sum conflict has
`|t| + |t'| ≤ n - 2` and a difference conflict `|t| + |t'| = n`.
-/

open Finset

namespace PointSets

variable {n : ℕ}

/-- Squares of the `n × n` board: (row, column). -/
abbrev Sq (n : ℕ) := Fin n × Fin n

/-- Flat sum `r + c`. -/
def fs (q : Sq n) : ℤ := (q.1 : ℤ) + (q.2 : ℤ)

/-- Flat difference `t = r - c`. -/
def fd (q : Sq n) : ℤ := (q.1 : ℤ) - (q.2 : ℤ)

/-- Sum conflict across the two flat pieces of a wrapped sum diagonal. -/
def SC (q q' : Sq n) : Prop := fs q % n = fs q' % n ∧ fs q ≠ fs q'

/-- Difference conflict across the two flat pieces of a wrapped difference diagonal. -/
def DC (q q' : Sq n) : Prop := fd q % n = fd q' % n ∧ fd q ≠ fd q'

theorem SC_symm {q q' : Sq n} (h : SC q q') : SC q' q := ⟨h.1.symm, h.2.symm⟩

theorem DC_symm {q q' : Sq n} (h : DC q q') : DC q' q := ⟨h.1.symm, h.2.symm⟩

/-- A nonzero multiple of `n` strictly between `-2n` and `2n` is `n` or `-n`. -/
theorem shift {d : ℤ} (h : (n : ℤ) ∣ d) (h1 : -(2 * n) < d) (h2 : d < 2 * n) (h0 : d ≠ 0) :
    d = n ∨ d = -n := by
  obtain ⟨k, rfl⟩ := h
  have hn : (0 : ℤ) ≤ n := by positivity
  have a : k < 2 := by
    by_contra hk; push Not at hk; nlinarith
  have b : -2 < k := by
    by_contra hk; push Not at hk; nlinarith
  interval_cases k <;> simp_all

/-- Lemma `dist`, sum case, for any two squares: `|t| + |t'| ≤ n - 2`. -/
theorem sum_t {q q' : Sq n} (h : SC q q') : |fd q| + |fd q'| ≤ (n : ℤ) - 2 := by
  have d := Int.ModEq.dvd h.1
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  have h3 := q'.1.isLt
  have h4 := q'.2.isLt
  unfold SC fs at h
  unfold fs at d
  have e := shift d (by omega) (by omega) (by intro e; exact h.2 (by omega))
  unfold fd
  rcases abs_cases ((q.1 : ℤ) - (q.2 : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases ((q'.1 : ℤ) - (q'.2 : ℤ)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega

/-- Lemma `dist`, difference case, for any two squares: `|t| + |t'| = n`. -/
theorem dif_t {q q' : Sq n} (h : DC q q') : |fd q| + |fd q'| = n := by
  have d := Int.ModEq.dvd h.1
  have h1 := q.1.isLt
  have h2 := q.2.isLt
  have h3 := q'.1.isLt
  have h4 := q'.2.isLt
  unfold DC fd at h
  unfold fd at d ⊢
  have e := shift d (by omega) (by omega) (by intro e; exact h.2 (by omega))
  rcases abs_cases ((q.1 : ℤ) - (q.2 : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases ((q'.1 : ℤ) - (q'.2 : ℤ)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega

section

variable (P : Finset (Sq n))

/-- At most two squares of `P` on each wrapped sum diagonal and on each wrapped difference diagonal. -/
def AtMostTwo : Prop :=
  (∀ a : ℤ, (P.filter (fun q => fs q % n = a)).card ≤ 2) ∧
    ∀ a : ℤ, (P.filter (fun q => fd q % n = a)).card ≤ 2

variable {P}

theorem SC_unique (h2 : AtMostTwo P) {q j k : Sq n} (hq : q ∈ P) (hj : j ∈ P) (hk : k ∈ P)
    (h1 : SC q j) (h3 : SC q k) : j = k := by
  by_contra hjk
  have hc := h2.1 (fs q % n)
  have : 2 < (P.filter (fun x => fs x % n = fs q % n)).card :=
    two_lt_card.mpr ⟨q, mem_filter.mpr ⟨hq, rfl⟩, j, mem_filter.mpr ⟨hj, h1.1.symm⟩,
      k, mem_filter.mpr ⟨hk, h3.1.symm⟩, fun e => h1.2 (by rw [e]), fun e => h3.2 (by rw [e]), hjk⟩
  omega

theorem DC_unique (h2 : AtMostTwo P) {q j k : Sq n} (hq : q ∈ P) (hj : j ∈ P) (hk : k ∈ P)
    (h1 : DC q j) (h3 : DC q k) : j = k := by
  by_contra hjk
  have hc := h2.2 (fd q % n)
  have : 2 < (P.filter (fun x => fd x % n = fd q % n)).card :=
    two_lt_card.mpr ⟨q, mem_filter.mpr ⟨hq, rfl⟩, j, mem_filter.mpr ⟨hj, h1.1.symm⟩,
      k, mem_filter.mpr ⟨hk, h3.1.symm⟩, fun e => h1.2 (by rw [e]), fun e => h3.2 (by rw [e]), hjk⟩
  omega

/-- **No closed set**: no nonempty subset of `P` holds, for each member, a sum-conflict partner and a
difference-conflict partner. -/
theorem no_closed_set (h2 : AtMostTwo P) (C : Finset (Sq n)) (hCP : C ⊆ P) (hC : C.Nonempty)
    (hsum : ∀ i ∈ C, ∃ j ∈ C, SC i j) (hdif : ∀ i ∈ C, ∃ j ∈ C, DC i j) : False := by
  classical
  choose! σ hσC hσ using hsum
  choose! δ hδC hδ using hdif
  have σσ : ∀ i ∈ C, σ (σ i) = i := fun i hi =>
    SC_unique h2 (hCP (hσC i hi)) (hCP (hσC _ (hσC i hi))) (hCP hi) (hσ _ (hσC i hi)) (SC_symm (hσ i hi))
  have δδ : ∀ i ∈ C, δ (δ i) = i := fun i hi =>
    DC_unique h2 (hCP (hδC i hi)) (hCP (hδC _ (hδC i hi))) (hCP hi) (hδ _ (hδC i hi)) (DC_symm (hδ i hi))
  have e1 : ∑ i ∈ C, |fd (σ i)| = ∑ i ∈ C, |fd i| :=
    sum_nbij' σ σ hσC hσC σσ σσ (fun _ _ => rfl)
  have e2 : ∑ i ∈ C, |fd (δ i)| = ∑ i ∈ C, |fd i| :=
    sum_nbij' δ δ hδC hδC δδ δδ (fun _ _ => rfl)
  have b1 : ∑ i ∈ C, (|fd i| + |fd (σ i)|) ≤ ∑ _i ∈ C, ((n : ℤ) - 2) :=
    sum_le_sum (fun i hi => sum_t (hσ i hi))
  have b2 : ∑ i ∈ C, (|fd i| + |fd (δ i)|) = ∑ _i ∈ C, (n : ℤ) :=
    sum_congr rfl (fun i hi => dif_t (hδ i hi))
  rw [sum_add_distrib, e1, sum_const, nsmul_eq_mul] at b1
  rw [sum_add_distrib, e2, sum_const, nsmul_eq_mul] at b2
  have hc : (0 : ℤ) < C.card := by exact_mod_cast hC.card_pos
  linarith

variable (P) in
/-- Conflict graph of `P`: squares of `P` joined by a conflict across flat pieces. -/
def conflictGraph : SimpleGraph (Sq n) where
  Adj q q' := q ∈ P ∧ q' ∈ P ∧ q ≠ q' ∧ (SC q q' ∨ DC q q')
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.imp SC_symm DC_symm⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

/-- Two distinct neighbours of `i` give one partner of each family. -/
theorem partners_of_two (h2 : AtMostTwo P) {i x y : Sq n} (hxy : x ≠ y) (hx : (conflictGraph P).Adj i x)
    (hy : (conflictGraph P).Adj i y) : (SC i x ∨ SC i y) ∧ (DC i x ∨ DC i y) := by
  obtain ⟨hi, hxP, _, hx⟩ := hx
  obtain ⟨_, hyP, _, hy⟩ := hy
  rcases hx with hxs | hxd <;> rcases hy with hys | hyd
  · exact absurd (SC_unique h2 hi hxP hyP hxs hys) hxy
  · exact ⟨Or.inl hxs, Or.inr hyd⟩
  · exact ⟨Or.inr hys, Or.inl hxd⟩
  · exact absurd (DC_unique h2 hi hxP hyP hxd hyd) hxy

/-- **No cycles for point sets** (Theorem `thm:cycles`, second part). -/
theorem acyclic (h2 : AtMostTwo P) : (conflictGraph P).IsAcyclic := by
  classical
  intro v c hc
  have hsub : c.support.toFinset ⊆ P := by
    intro i hi
    rw [List.mem_toFinset] at hi
    obtain ⟨x, y, _, hset⟩ := Set.ncard_eq_two.mp (hc.ncard_neighborSet_toSubgraph_eq_two hi)
    have hxa : c.toSubgraph.Adj i x := by
      rw [← SimpleGraph.Subgraph.mem_neighborSet, hset]; simp
    exact hxa.adj_sub.1
  have key : ∀ i ∈ c.support.toFinset, (∃ j ∈ c.support.toFinset, SC i j) ∧
      (∃ j ∈ c.support.toFinset, DC i j) := by
    intro i hi
    rw [List.mem_toFinset] at hi
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp (hc.ncard_neighborSet_toSubgraph_eq_two hi)
    have hxa : c.toSubgraph.Adj i x := by
      rw [← SimpleGraph.Subgraph.mem_neighborSet, hset]; simp
    have hya : c.toSubgraph.Adj i y := by
      rw [← SimpleGraph.Subgraph.mem_neighborSet, hset]; simp
    have hxm : x ∈ c.support.toFinset := by
      rw [List.mem_toFinset, ← SimpleGraph.Walk.mem_verts_toSubgraph]; exact hxa.snd_mem
    have hym : y ∈ c.support.toFinset := by
      rw [List.mem_toFinset, ← SimpleGraph.Walk.mem_verts_toSubgraph]; exact hya.snd_mem
    obtain ⟨h1, h3⟩ := partners_of_two h2 hxy hxa.adj_sub hya.adj_sub
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · exact ⟨x, hxm, h⟩
      · exact ⟨y, hym, h⟩
    · rcases h3 with h | h
      · exact ⟨x, hxm, h⟩
      · exact ⟨y, hym, h⟩
  exact no_closed_set h2 c.support.toFinset hsub ⟨v, by simp⟩ (fun i hi => (key i hi).1)
    (fun i hi => (key i hi).2)

end

end PointSets

#print axioms PointSets.acyclic
