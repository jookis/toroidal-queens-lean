import QueensLean.Levels
import QueensLean.BoardCheck

/-!
# Controls for the forbidden levels

The hypotheses of `Levels.levels` matter: two conflicts occur at the composite sizes `25` and `35` (Remark
`rem:level2`, boards from `paper/code/level2_examples_check.py`), and three conflicts at `n = 12`, which is even but
not twice a prime. Each board is checked by `Boards.check` with `decide +kernel`.
-/

namespace LevelsControls

open Queens Ceiling Boards

theorem two_at_25 : ∃ p : Equiv.Perm (Fin 25), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
    conf p = 2 :=
  sound (L := [19, 0, 11, 8, 14, 1, 6, 13, 24, 16, 12, 4, 23, 21, 15, 2, 5, 7, 10, 22, 18, 9, 17, 20, 3])
    (by decide +kernel)

theorem two_at_35 : ∃ p : Equiv.Perm (Fin 35), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
    conf p = 2 :=
  sound (L := [27, 5, 10, 19, 11, 33, 3, 32, 6, 9, 22, 31, 17, 23, 16, 18, 29, 34, 13, 2, 0, 7, 21, 12, 30, 1,
    14, 28, 24, 8, 4, 15, 26, 20, 25]) (by decide +kernel)

theorem three_at_12 : ∃ p : Equiv.Perm (Fin 12), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
    conf p = 3 :=
  sound (L := [0, 2, 4, 10, 7, 9, 11, 3, 1, 6, 8, 5]) (by decide +kernel)

end LevelsControls

#print axioms LevelsControls.two_at_35
