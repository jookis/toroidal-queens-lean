import QueensLean.Layer
import QueensLean.BoardCheck

/-!
# Control for the crystal layer (Example `ex:75`)

At `n = 75` (floor `2`) the board of Example `ex:75` has exactly two conflicts, so it sits on the floor, and its sum
classes are balanced modulo the prime `5` (as `Layer.layer` says) but not modulo `25`: residue `1` modulo `25`
holds only two sum classes instead of three. So Theorem `thm:layer` does not extend to all divisors of `n`.
-/

namespace LayerControls

open Queens Ceiling Boards Layer

/-- The board of Example `ex:75`. -/
def L75 : List ℕ := [38, 45, 62, 51, 9, 36, 72, 21, 3, 24, 30, 64, 59, 31, 47, 15, 44, 20, 0, 43, 28, 10, 73, 49,
  1, 52, 58, 7, 57, 54, 17, 48, 11, 19, 5, 33, 6, 50, 35, 14, 41, 63, 32, 26, 67, 13, 55, 8, 42, 53, 71, 16, 18, 46,
  56, 65, 40, 68, 39, 23, 34, 2, 74, 69, 60, 27, 25, 22, 12, 29, 37, 70, 4, 61, 66]

theorem ex75 : ∃ p : Equiv.Perm (Fin 75), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
    conf p = floorVal 75 ∧ bal (sumCls p) (show 5 ∣ 75 by norm_num) ∧ ¬ bal (sumCls p) (show 25 ∣ 75 by norm_num) := by
  obtain ⟨p, hs, hd, hc, hp⟩ := sound_val (n := 75) (k := 2) (L := L75) (by decide +kernel)
  have hf : floorVal 75 = 2 := by decide
  refine ⟨p, hs, hd, by rw [hc, hf], (layer p (by rw [hc, hf]) (by norm_num) le_rfl (by norm_num)).1, ?_⟩
  intro hb
  have h1 := hb 1
  have e : ∀ i, sumCls p i = (((i : ℕ) + colsF 75 L75 i : ℕ) : ZMod 75) := by
    intro i; unfold sumCls; rw [hp]; push_cast; rfl
  simp_rw [e] at h1
  revert h1
  decide +kernel

end LayerControls

#print axioms LayerControls.ex75
