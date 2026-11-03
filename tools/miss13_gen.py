"""Generate the C(13) = 7 kernel proof split by the first four rows.

One file QueensLeanHeavy/Miss13/P_a_b.lean per safe two-row prefix [a, b]: a `decide +kernel` theorem m13_a_b_c_d for every
safe four-row prefix, then the glues m13_a_b_c and m13_a_b. (Three-row pieces ran out of memory at 23 GB; one
four-row piece takes about 10 s.) MissC13.lean glues m13_a_b into m13_a and m13_a into go13.
Every case is a separate bullet after `interval_cases`, so no `exact` is ever tried against the wrong prefix.
Usage: miss13_gen.py OUTDIR  (OUTDIR = the QueensLeanHeavy source folder).
"""
import os, sys

N, K = 13, 7


def safe(L, c):
    r = len(L)
    return all(x != c and i + x != r + c and i + c != r + x for i, x in enumerate(L))


def glue(name, goal_rows, L, child):
    lst = "[" + ", ".join(map(str, L)) + "]"
    out = [f"theorem {name} : go {N} {K} {goal_rows} {lst} = true := go_of fun c hc hs => by",
           "  interval_cases c"]
    for c in range(N):
        out.append(f"  · exact {child(c)}" if safe(L, c) else "  · exact absurd hs (by decide)")
    return out


def main(outdir):
    os.makedirs(os.path.join(outdir, "Miss13"), exist_ok=True)
    pairs = [(a, b) for a in range(N) for b in range(N) if safe([a], b)]
    for a, b in pairs:
        lines = ["import QueensLean.Misses", "", f"/-! Prefix searches for `C(13)` under the rows [{a}, {b}]. -/", "",
                 "namespace Misses", "", "set_option maxHeartbeats 0", "set_option Elab.async false", ""]
        for c in range(N):
            if safe([a, b], c):
                for d in range(N):
                    if safe([a, b, c], d):
                        lines.append(f"theorem m13_{a}_{b}_{c}_{d} : go {N} {K} {N - 4} [{a}, {b}, {c}, {d}] = true := "
                                     "by decide +kernel")
                lines.append("")
                lines += glue(f"m13_{a}_{b}_{c}", N - 3, [a, b, c], lambda d, c=c: f"m13_{a}_{b}_{c}_{d}") + [""]
        lines += glue(f"m13_{a}_{b}", N - 2, [a, b], lambda c: f"m13_{a}_{b}_{c}")
        lines += ["", "end Misses", ""]
        open(os.path.join(outdir, "Miss13", f"P_{a}_{b}.lean"), "w").write("\n".join(lines))
    top = [f"import QueensLeanHeavy.Miss13.P_{a}_{b}" for a, b in pairs]
    top += ["", "/-! `C(13) = 7` by kernel search, split by the first four rows (one `decide` per prefix). -/", "",
            "namespace Misses", "", "open Queens Ceiling Boards", ""]
    for a in range(N):
        top += glue(f"m13_{a}", N - 1, [a], lambda c, a=a: f"m13_{a}_{c}") + [""]
    top += glue("go13", N, [], lambda c: f"m13_{c}") + [""]
    top += ["/-- **`C(13) = 7`**, one below `⌊13/φ⌋ = 8`. -/",
            "theorem C_13 : ⌊(13 : ℝ) / Real.goldenRatio⌋ = 8 ∧",
            "    (∃ p : Equiv.Perm (Fin 13), Function.Injective (vs p) ∧ Function.Injective (vd p) ∧ conf p = 7) ∧",
            "    ∀ p : Equiv.Perm (Fin 13), Function.Injective (vs p) → Function.Injective (vd p) → conf p ≤ 7 :=",
            "  ⟨floor_eq_of (by norm_num) (by norm_num), sound (L := [1, 3, 8, 11, 4, 10, 5, 0, 12, 7, 2, 6, 9]) (by decide +kernel),",
            "    fun p hs hd => go_sound go13 p hs hd⟩", "", "end Misses", "", "#print axioms Misses.C_13", ""]
    open(os.path.join(outdir, "MissC13.lean"), "w").write("\n".join(top))
    n4 = sum(safe([a, b, c], d) for a, b in pairs for c in range(N) if safe([a, b], c) for d in range(N))
    print(f"{len(pairs)} files, {n4} four-row theorems")


if __name__ == "__main__":
    main(sys.argv[1])
