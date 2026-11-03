"""Floor constructions for Lean (2026-10-18): cut each completed Monsky board into runs with affine reduced
coordinates and fit them affine in t' for n = M t' + c. Prototype: prints the run structure per class."""
import sys
from fractions import Fraction
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "scripts"))
from monsky_complete import placement
from monsky_completion import extra

def queens(n):
    """Completed board as an ordered list of queens (X, Y) after the cut: Monsky's queens in string order, then the
    added queens. X = column, Y = row, both in [0, n)."""
    q, (dx, dy) = extra(n)
    return [((x + dx) % n, (y + dy) % n) for x, y in placement(n) + q], len(q)

def runs(n, g):
    """Maximal runs of consecutive Monsky queens with step exactly g in reduced coordinates; added queens alone."""
    Q, a = queens(n); old = Q[:len(Q) - a]; out = []; st = 0
    for i in range(1, len(old) + 1):
        if i == len(old) or (old[i][0] - old[i - 1][0], old[i][1] - old[i - 1][1]) != g:
            out.append((old[st][0], old[st][1], i - 1 - st, g)); st = i
    for x, y in Q[len(Q) - a:]: out.append((x, y, 0, g))
    return out, a

def fit(M, c, T0, g, count=6):
    """Affine fit of every run's (X0, Y0, len) in t' over t' = T0..T0+count; None if the structure changes."""
    data = [runs(M * t + c, g)[0] for t in range(T0, T0 + count)]
    if len({len(d) for d in data}) != 1: return None
    res = []
    for j in range(len(data[0])):
        coefs = []
        for f in range(3):
            v0, v1 = data[0][j][f], data[1][j][f]; a = v1 - v0; b = v0 - a * T0
            if any(a * (T0 + i) + b != data[i][j][f] for i in range(count)): return None
            coefs.append((a, b))
        res.append(tuple(coefs))
    return res

if __name__ == "__main__":
    CLASSES = [(12, 2), (12, 10), (12, 3), (12, 9), (12, 4), (24, 6), (24, 18), (24, 8), (24, 20), (12, 0)]
    FIRST = {2: 14, 10: 10, 3: 15, 9: 21, 4: 16, 6: 30, 18: 18, 8: 32, 20: 20, 0: 24}
    for P, r in CLASSES:
        m = 2 if r % 2 else 3; M = P * m; g = (1, 2) if r % 2 else (1, 3)
        for s in range(m):
            c = P * s + r
            T = 0
            while M * T + c < FIRST[r]: T += 1
            # find the first T from which the structure is stable (checked over 6 points, then a long check)
            T1 = T
            while fit(M, c, T1, g) is None and T1 < T + 10: T1 += 1
            F = fit(M, c, T1, g, count=12)
            print(f"n = {M}t'+{c}: first n {M*T+c}, stable from n = {M*T1+c}: {len(F) if F else 'NO FIT'} runs")

def family(P, r, s):
    """Fitted family for n = M t' + c, written in u = t' - T1: run data affine in u, plus Bs/Bd (indices of added
    queens whose sum / difference class meets an old queen). Checked against the real boards for u = 0..30."""
    m = 2 if r % 2 else 3; M = P * m; g = (1, 2) if r % 2 else (1, 3); c = P * s + r
    FIRST = {2: 14, 10: 10, 3: 15, 9: 21, 4: 16, 6: 30, 18: 18, 8: 32, 20: 20, 0: 24}
    T = 0
    while M * T + c < FIRST[r]: T += 1
    T1 = T
    while fit(M, c, T1, g, count=12) is None: T1 += 1
    F = fit(M, c, T1, g, count=12)
    n0 = M * T1 + c
    runs_u = []
    for (ax, bx), (ay, by), (al, bl) in F:
        x = (ax, ax * T1 + bx); y = (ay, ay * T1 + by); L = (al, al * T1 + bl + 1)   # L = number of queens
        assert all(v[0] >= 0 and v[1] >= 0 for v in (x, y, L)) and L[1] >= 1, (P, r, s, x, y, L)
        runs_u.append((x, y, L))
    K = len(runs_u); a = runs(n0, g)[1]
    steps = [g] * (K - a) + [(0, 0)] * a
    def board(u):
        n = M * u + n0; Q = []
        for j, ((xa, xb), (ya, yb), (la, lb)) in enumerate(runs_u):
            for k in range(la * u + lb): Q.append((xa * u + xb + steps[j][0] * k, ya * u + yb + steps[j][1] * k, j))
        return n, Q
    Bs, Bd = set(), set()
    for u in range(31):
        n, Q = board(u)
        real, _ = queens(n)
        assert sorted((x, y) for x, y, _ in Q) == sorted(real), (P, r, s, u)
        for x, y, j in Q:
            if j < K - a: continue
            for x2, y2, j2 in Q:
                if j2 >= K - a: continue
                if (x + y - x2 - y2) % n == 0: Bs.add(j)
                if (x - y - x2 + y2) % n == 0: Bd.add(j)
    return dict(M=M, n0=n0, K=K, runs=runs_u, steps=steps, Bs=sorted(Bs), Bd=sorted(Bd), first=M * T + c)

def lean_family(fam, name):
    M, n0, K = fam["M"], fam["n0"], fam["K"]
    lin = lambda v: f"{v[0]} * u + {v[1]}" if v[0] else f"{v[1]}"
    vec = lambda xs: "![" + ", ".join(xs) + "]"
    n = f"{M} * u + {n0}"
    F = 0 if n0 % 6 in (1, 5) else (3 if n0 % 6 == 0 else 2)
    assert len(fam["Bs"]) + len(fam["Bd"]) == F, (name, fam["Bs"], fam["Bd"], F)
    fs = lambda S: "{" + ", ".join(str(j) for j in S) + "}" if S else "∅"
    sim = "simp [X, Y, x0, y0, gx, gy, len, Bs, Bd, Xor, Finset.mem_filter, Finset.mem_univ, true_and] at *"
    return f'''
namespace {name}

open Queens Ceiling Construct

/-! `n = {n}`: {K} runs of queens (start column, start row, number of queens, step). -/

def len (u : ℕ) : Fin {K} → ℕ := {vec([lin(L) for _, _, L in fam["runs"]])}
def x0 (u : ℕ) : Fin {K} → ℕ := {vec([lin(x) for x, _, _ in fam["runs"]])}
def y0 (u : ℕ) : Fin {K} → ℕ := {vec([lin(y) for _, y, _ in fam["runs"]])}
def gx : Fin {K} → ℕ := {vec([str(s[0]) for s in fam["steps"]])}
def gy : Fin {K} → ℕ := {vec([str(s[1]) for s in fam["steps"]])}
abbrev I (u : ℕ) := Σ j : Fin {K}, Fin (len u j)
def X (u : ℕ) (a : I u) : ℕ := x0 u a.1 + gx a.1 * a.2
def Y (u : ℕ) (a : I u) : ℕ := y0 u a.1 + gy a.1 * a.2
def Bs (u : ℕ) : Finset (I u) := Finset.univ.filter fun a => a.1 ∈ ({fs(fam["Bs"])} : Finset (Fin {K}))
def Bd (u : ℕ) : Finset (I u) := Finset.univ.filter fun a => a.1 ∈ ({fs(fam["Bd"])} : Finset (Fin {K}))

theorem card (u : ℕ) : Fintype.card (I u) = {n} := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [Fin.sum_univ_succ, len]
  ring

theorem hX (u : ℕ) (a : I u) : X u a < {n} := by
  obtain ⟨j, k⟩ := a
  have := k.isLt
  fin_cases j <;> {sim} <;> omega

theorem hY (u : ℕ) (a : I u) : Y u a < {n} := by
  obtain ⟨j, k⟩ := a
  have := k.isLt
  fin_cases j <;> {sim} <;> omega

theorem h1 (u : ℕ) (a b : I u) (h : a ≠ b) :
    X u a ≠ X u b ∧ Y u a ≠ Y u b ∧ X u a + Y u a ≠ X u b + Y u b ∧ X u a + Y u b ≠ X u b + Y u a := by
  have h' := sig_ne h
  clear h
  obtain ⟨j1, k1⟩ := a
  obtain ⟨j2, k2⟩ := b
  have := k1.isLt
  have := k2.isLt
  fin_cases j1 <;> fin_cases j2 <;> {sim} <;> omega

set_option trace.Meta.Tactic.simp false in
theorem hs (u : ℕ) (a b : I u) (h : a ≠ b) (e : X u a + Y u a = X u b + Y u b + ({n})) :
    Xor (a ∈ Bs u) (b ∈ Bs u) := by
  simp only [Bs, Finset.mem_filter, Finset.mem_univ, true_and]
  have h' := sig_ne h
  clear h
  obtain ⟨j1, k1⟩ := a
  obtain ⟨j2, k2⟩ := b
  have := k1.isLt
  have := k2.isLt
  fin_cases j1 <;> fin_cases j2 <;> {sim} <;> omega

theorem hd (u : ℕ) (a b : I u) (h : a ≠ b) (e : Y u a + X u b = Y u b + X u a + ({n})) :
    Xor (a ∈ Bd u) (b ∈ Bd u) := by
  simp only [Bd, Finset.mem_filter, Finset.mem_univ, true_and]
  have h' := sig_ne h
  clear h
  obtain ⟨j1, k1⟩ := a
  obtain ⟨j2, k2⟩ := b
  have := k1.isLt
  have := k2.isLt
  fin_cases j1 <;> fin_cases j2 <;> {sim} <;> omega

/-- **Floor solution** at every `n = {n}`. -/
theorem floor_sol (u : ℕ) : ∃ p : Equiv.Perm (Fin ({n})), Function.Injective (vs p) ∧
    Function.Injective (vd p) ∧ conf p = Layer.floorVal ({n}) := by
  have : NeZero ({n}) := ⟨by omega⟩
  obtain ⟨p, h2, h3, hc⟩ := build (X u) (Y u) (card u) (hX u) (hY u) (h1 u) (Bs u) (Bd u) (hs u) (hd u)
  have hB : (Bs u).card + (Bd u).card = {F} := by simp only [Bs, Bd, card_fst]; simp [len]
  have hf : Layer.floorVal ({n}) = {F} := by
    rw [floorVal_mod]
    have : ({n}) % 6 = {n0 % 6} := by omega
    simp [this]
  exact ⟨p, h2, h3, le_antisymm (hf ▸ hB ▸ hc) (floor_le_conf p)⟩

end {name}
'''
