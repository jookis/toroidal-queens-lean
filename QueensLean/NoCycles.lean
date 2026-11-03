import QueensLean.Ceiling

/-!
# No conflict cycles

Lean target 5 (2026-10-18) for "The fewest and the most toroidal conflicts" (Theorem `thm:cycles`). For an
`n`-queens solution `p` (distinct flat sums `vs p` and flat differences `vd p`), `no_closed_set`: no nonempty set of
queens has, for every member, a sum partner and a difference partner inside the set; `acyclic`: the conflict graph
(rows, joined when they share a wrapped sum or difference class) has no cycle (`SimpleGraph.IsAcyclic`).
The proof is the paper's: with `t = r - c`, a sum conflict has `|t| + |t'| ≤ n - 2` and a difference conflict
`|t| + |t'| = n`; summing `|t|` over the set through both partner maps gives `(n - 2)|C| ≥ n|C|`.
-/

open Finset

namespace NoCycles

open Queens Ceiling

variable {n : ℕ} {p : Equiv.Perm (Fin n)}

/-- `j` is a sum partner of `i`. -/
def SP (p : Equiv.Perm (Fin n)) (i j : Fin n) : Prop := j ≠ i ∧ sumCls p j = sumCls p i

/-- `j` is a difference partner of `i`. -/
def DP (p : Equiv.Perm (Fin n)) (i j : Fin n) : Prop := j ≠ i ∧ difCls p j = difCls p i

theorem SP_symm {i j : Fin n} (h : SP p i j) : SP p j i := ⟨h.1.symm, h.2.symm⟩

theorem DP_symm {i j : Fin n} (h : DP p i j) : DP p j i := ⟨h.1.symm, h.2.symm⟩

theorem SP_unique (hs : Function.Injective (vs p)) {i j k : Fin n} (hj : SP p i j) (hk : SP p i k) :
    j = k := by
  have h := w_le_one hs 0 (vs_range p) (sum_dvd p) i
  unfold w at h
  exact card_le_one.mp h j (by simp [hj.1, hj.2]) k (by simp [hk.1, hk.2])

theorem DP_unique (hd : Function.Injective (vd p)) {i j k : Fin n} (hj : DP p i j) (hk : DP p i k) :
    j = k := by
  have h := w_le_one hd _ (vd_range p) (dif_dvd p) i
  unfold w at h
  exact card_le_one.mp h j (by simp [hj.1, hj.2]) k (by simp [hk.1, hk.2])

/-- Lemma `dist`, sum case: `|t| + |t'| ≤ n - 2`. -/
theorem sum_t (hs : Function.Injective (vs p)) {i j : Fin n} (hij : i ≠ j)
    (h : sumCls p i = sumCls p j) : |vd p i| + |vd p j| ≤ (n : ℤ) - 2 := by
  have g := gap hs 0 (vs_range p) hij (sum_dvd p i j h)
  have h1 := i.isLt
  have h2 := j.isLt
  have h3 := (p i).isLt
  have h4 := (p j).isLt
  unfold vs at g
  unfold vd
  rcases abs_cases ((i : ℕ) - ((p i : ℕ) : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases abs_cases ((j : ℕ) - ((p j : ℕ) : ℤ)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;> omega

/-- Lemma `dist`, difference case: `|t| + |t'| = n`. -/
theorem dif_t (hd : Function.Injective (vd p)) {i j : Fin n} (hij : i ≠ j)
    (h : difCls p i = difCls p j) : |vd p i| + |vd p j| = n := by
  have := dist hd _ (vd_range p) hij (dif_dvd p i j h)
  simpa using this

/-- **No closed set**: no nonempty set of queens holds, for each member, a sum partner and a difference
partner. -/
theorem no_closed_set (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p))
    (C : Finset (Fin n)) (hC : C.Nonempty) (hsum : ∀ i ∈ C, ∃ j ∈ C, SP p i j)
    (hdif : ∀ i ∈ C, ∃ j ∈ C, DP p i j) : False := by
  classical
  choose! σ hσC hσ using hsum
  choose! δ hδC hδ using hdif
  have σσ : ∀ i ∈ C, σ (σ i) = i := fun i hi => SP_unique hs (hσ _ (hσC i hi)) (SP_symm (hσ i hi))
  have δδ : ∀ i ∈ C, δ (δ i) = i := fun i hi => DP_unique hd (hδ _ (hδC i hi)) (DP_symm (hδ i hi))
  have e1 : ∑ i ∈ C, |vd p (σ i)| = ∑ i ∈ C, |vd p i| :=
    sum_nbij' σ σ hσC hσC σσ σσ (fun _ _ => rfl)
  have e2 : ∑ i ∈ C, |vd p (δ i)| = ∑ i ∈ C, |vd p i| :=
    sum_nbij' δ δ hδC hδC δδ δδ (fun _ _ => rfl)
  have b1 : ∑ i ∈ C, (|vd p i| + |vd p (σ i)|) ≤ ∑ _i ∈ C, ((n : ℤ) - 2) :=
    sum_le_sum (fun i hi => sum_t hs (hσ i hi).1.symm (hσ i hi).2.symm)
  have b2 : ∑ i ∈ C, (|vd p i| + |vd p (δ i)|) = ∑ _i ∈ C, (n : ℤ) :=
    sum_congr rfl (fun i hi => dif_t hd (hδ i hi).1.symm (hδ i hi).2.symm)
  rw [sum_add_distrib, e1, sum_const, nsmul_eq_mul] at b1
  rw [sum_add_distrib, e2, sum_const, nsmul_eq_mul] at b2
  have hc : (0 : ℤ) < C.card := by exact_mod_cast hC.card_pos
  linarith

/-- The conflict graph of `p`: rows joined when they share a wrapped sum or difference class. -/
def conflictGraph (p : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (sumCls p i = sumCls p j ∨ difCls p i = difCls p j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp Eq.symm Eq.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Two distinct neighbours of `i` in a set give one partner of each family in that set. -/
theorem partners_of_two (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) {i x y : Fin n}
    (hxy : x ≠ y) (hx : (conflictGraph p).Adj i x) (hy : (conflictGraph p).Adj i y) :
    (SP p i x ∨ SP p i y) ∧ (DP p i x ∨ DP p i y) := by
  obtain ⟨hix, hx⟩ := hx
  obtain ⟨hiy, hy⟩ := hy
  rcases hx with hxs | hxd <;> rcases hy with hys | hyd
  · exact absurd (SP_unique hs ⟨hix.symm, hxs.symm⟩ ⟨hiy.symm, hys.symm⟩) hxy
  · exact ⟨Or.inl ⟨hix.symm, hxs.symm⟩, Or.inr ⟨hiy.symm, hyd.symm⟩⟩
  · exact ⟨Or.inr ⟨hiy.symm, hys.symm⟩, Or.inl ⟨hix.symm, hxd.symm⟩⟩
  · exact absurd (DP_unique hd ⟨hix.symm, hxd.symm⟩ ⟨hiy.symm, hyd.symm⟩) hxy

/-- **No conflict cycles**: the conflict graph of an `n`-queens solution is acyclic. -/
theorem acyclic (hs : Function.Injective (vs p)) (hd : Function.Injective (vd p)) :
    (conflictGraph p).IsAcyclic := by
  classical
  intro v c hc
  have key : ∀ i ∈ c.support.toFinset, (∃ j ∈ c.support.toFinset, SP p i j) ∧
      (∃ j ∈ c.support.toFinset, DP p i j) := by
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
    obtain ⟨h1, h2⟩ := partners_of_two hs hd hxy hxa.adj_sub hya.adj_sub
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · exact ⟨x, hxm, h⟩
      · exact ⟨y, hym, h⟩
    · rcases h2 with h | h
      · exact ⟨x, hxm, h⟩
      · exact ⟨y, hym, h⟩
  exact no_closed_set hs hd c.support.toFinset ⟨v, by simp⟩ (fun i hi => (key i hi).1)
    (fun i hi => (key i hi).2)

end NoCycles

#print axioms NoCycles.no_closed_set
#print axioms NoCycles.acyclic
