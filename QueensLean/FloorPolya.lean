import QueensLean.Construct

/-!
# Floor solutions for `gcd(n, 6) = 1`: Pólya's board `p(i) = 2i mod n`

It has no toroidal conflicts at all, so it is a legal flat solution with `f(n) = 0` conflicts.
-/

namespace Construct

open Queens Ceiling

/-- Cancel a factor `c` coprime to `n` in `ZMod n`. -/
theorem cancel {n c : ℕ} (hc : Nat.Coprime c n) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : ((c * i : ℕ) : ZMod n) = ((c * j : ℕ) : ZMod n)) : i = j := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem polya_sol {n : ℕ} [NeZero n] (h : n % 6 = 1 ∨ n % 6 = 5) :
    ∃ p : Equiv.Perm (Fin n), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧
      conf p = Layer.floorVal n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have c1 : Nat.Coprime 1 n := Nat.coprime_one_left n
  have c2 : Nat.Coprime 2 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have c3 : Nat.Coprime 3 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
  let X : Fin n → ℕ := fun i => i
  let Y : Fin n → ℕ := fun i => 2 * i % n
  have cY : ∀ i : Fin n, ((Y i : ℕ) : ZMod n) = 2 * ((i : ℕ) : ZMod n) := by
    intro i; simp [Y, ZMod.natCast_mod]
  have toZ : ∀ {a b : ℕ}, a = b → (a : ZMod n) = b := fun e => by rw [e]
  have key : ∀ (c : ℕ), Nat.Coprime c n → ∀ i j : Fin n,
      (c : ZMod n) * ((i : ℕ) : ZMod n) = (c : ZMod n) * ((j : ℕ) : ZMod n) → i = j := by
    intro c hc i j e
    exact Fin.ext (cancel hc i.isLt j.isLt (by push_cast; exact e))
  obtain ⟨p, h2, h3, hc⟩ := build (n := n) X Y (Fintype.card_fin n) (fun i => i.isLt)
    (fun i => Nat.mod_lt _ hn)
    (by
      intro i j hij
      refine ⟨fun e => hij (Fin.ext e), fun e => hij ?_, fun e => hij ?_, fun e => hij ?_⟩
      · have := toZ e; rw [cY, cY] at this
        exact key 2 c2 i j (by exact_mod_cast this)
      · have := toZ e; push_cast [X] at this; rw [cY, cY] at this
        exact key 3 c3 i j (by push_cast; linear_combination this)
      · have := toZ e; push_cast [X] at this; rw [cY, cY] at this
        exact key 1 c1 i j (by push_cast; linear_combination -this))
    ∅ ∅
    (by
      intro i j hij e
      exfalso; apply hij
      have := toZ e; push_cast [X] at this; rw [cY, cY, ZMod.natCast_self] at this
      exact key 3 c3 i j (by push_cast; linear_combination this))
    (by
      intro i j hij e
      exfalso; apply hij
      have := toZ e; push_cast [X] at this; rw [cY, cY, ZMod.natCast_self] at this
      exact key 1 c1 i j (by push_cast; linear_combination this))
  refine ⟨p, h2, h3, ?_⟩
  have : Layer.floorVal n = 0 := by rw [floorVal_mod, if_pos h]
  simp at hc; omega

end Construct
