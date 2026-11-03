# toroidal-queens-lean

Lean 4 proofs (with mathlib) for the papers on toroidal conflicts of n-queens solutions by Jouko Kines.

On an n x n board whose edges wrap around (a torus), the queens of an ordinary n-queens solution can still meet on the
wrapped diagonals. These files prove, from the definitions alone, what the fewest and the most such conflicts are.
No `sorry`; every listed theorem uses only the three standard axioms `propext`, `Classical.choice`, `Quot.sound`.

## Start here

`SecondLean/Spec.lean` is the file to read. It defines everything again straight from the board, with no encodings:

- a board is `f : Fin n → Fin n` (row i holds a queen in column f i);
- a solution: no two queens share a column, and `|i - j| ≠ |f i - f j|` for any two rows;
- the wrapped diagonals of a queen are `(i + f i) mod n` and `(i + n - f i) mod n`;
- a conflict is a pair of queens on the same wrapped diagonal.

It then proves these definitions equal to the compact ones the proofs use (`isSolution_iff`, `confSpec_eq`,
`graphSpec_eq`), restates the main results with the plain definitions only (`floor`, `levels`, `union_of_paths`,
`golden_ceiling`), and checks them on explicit boards (n = 4, 5, 6 and the n = 26 board of the paper, plus two
boards that must fail). A reader who trusts these lines can leave the rest to the checkers.

## Papers

| Paper | Lean | Tag | Archived bundle |
|---|---|---|---|
| The fewest and the most toroidal conflicts of an n-queens solution (v4) | `QueensLean`, `QueensLeanHeavy` | `paper1-v4` | Zenodo [10.5281/zenodo.23755751](https://doi.org/10.5281/zenodo.23755751) |
| Specification of paper 1 and its Theorem 5 in full | `SecondLean/Spec.lean`, `SecondLean/Paths.lean` | (after `paper1-v4`) | with paper 2 |
| Paper 2 (in preparation) | `SecondLean` | at its release | at its release |

Each tag is the exact code its paper cites. The Zenodo bundles also hold the Python computations, data and boards,
which are not repeated here. `docs/paper1-bundle-README.md` is paper 1's Lean README from its bundle (its relative
paths point into that bundle), with the full paper-to-Lean table.

## Main results of paper 1 in Lean

| Paper | Lean |
|---|---|
| Theorem 2: the fewest conflicts is exactly 0, 2 or 3 | `Construct.floor_exact`; plain form `SecondLean.Spec.floor` |
| Theorem 3: never 1; never 2 at prime n ≥ 5; never 3 at n = 2q | `Levels.levels`; plain form `SecondLean.Spec.levels` |
| Theorem 4: balanced modulo every prime K ≥ 5 dividing n | `Layer.layer`, `Layer.layer_even` |
| Theorem 5: the conflict graph is a union of paths | `NoCycles.acyclic`, `SecondLean.Paths.union_of_paths`; plain form `SecondLean.Spec.union_of_paths` |
| Theorem 17: at most floor(n/φ) conflicts | `Golden.golden_ceiling`; plain form `SecondLean.Spec.golden_ceiling` |
| Corollary 19: exact maxima at the listed sizes (C(10) = 5 and C(13) = 7 by kernel searches) | `Ceilings.C_n`, `CeilingsRouteA`, `QueensLeanHeavy` |

`QueensLean/MainResults.lean` restates every result of paper 1 in its own notation.

## Build

Toolchain `leanprover/lean4:v4.36.0-rc1`, mathlib at tag v4.36.0-rc1 (pinned in `lake-manifest.json`).

    lake exe cache get          # precompiled mathlib (several GB)
    lake build                  # QueensLean and SecondLean (about 20 minutes)
    lake build QueensLeanHeavy  # optional: C(10) needs about 21 GB of memory, C(13) about 10 h on one core

## Checks

| Check | What it confirms | How to run | When |
|---|---|---|---|
| Lean kernel | every proof, during the build | `lake build` | every push (GitHub Actions) |
| Trust checks (`scripts/leankit.py`) | no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe` in the sources; only the three standard axioms for every theorem in `scripts/theorems.txt`; every theorem of the main files listed; the spec's sanity boards recomputed by an independent Python version (`scripts/plugins/queens.py`) | `scripts/check.sh` | every push |
| leanchecker | Lean's kernel replays every compiled module from scratch | `scripts/recheck.sh leanchecker` | every push |
| nanoda | an independent type checker written in Rust checks an export (lean4export) of each theorem and everything it uses, with only the three standard axioms permitted | `scripts/recheck.sh nanoda` | at each tag, by hand |

The checkers are the toolchain's own binaries (nanoda 0.4.17, lean4export 3.1.0 for the runs recorded so far); they
are referenced, not copied. `CHECKS.md` records every run: date, tag, checker, version, what was covered, result.

## License

Apache-2.0 (`LICENSE`).
