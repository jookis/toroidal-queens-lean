# Check record

Every run of the checks in the README, newest first. Paper 1's results before this repo existed come from its release
pipeline on the v4 bundle (sources byte-identical to tag `paper1-v4`).

| Date | Code | Checker (version) | Covered | Result |
|---|---|---|---|---|
| 2026-11-03 | main with the mathlib style linter off (lakefile only), clean copy | Lean kernel, `scripts/check.sh`, leanchecker | `lake build` 642 s, 0 style warnings, 0 errors; 118 theorems; 22 modules | PASS, standard axioms only |
| 2026-11-03 | main df2438f, GitHub Actions (ubuntu-latest, mathlib from cache.mathlib.org) | Lean kernel, `scripts/check.sh`, leanchecker | `lake build`; trust checks; 22 modules | PASS (green run, reported by the author) |
| 2026-11-03 | this repo before its first push (paper1-v4 plus Spec, Paths), clean copy, mathlib from pinned revs | Lean kernel (v4.36.0-rc1) | `lake build` (QueensLean, SecondLean), 642 s | PASS |
| 2026-11-03 | same | `scripts/check.sh` (leankit) | 157 source files; axioms of 118 theorems; 37 theorems of the main files listed; 10 spec board values recomputed | PASS, standard axioms only; controls (a `sorry` file, a wrong board count) fail as they should |
| 2026-11-03 | same | leanchecker (toolchain) | 22 modules of QueensLean and SecondLean (import-only roots skipped) | PASS 22/22 |
| 2026-10-29 | v4 bundle 85c4246d (= `paper1-v4`) | nanoda 0.4.17 on lean4export 3.1.0 | C(13) glue `Misses.C_13` with all 132 prefix files | PASS (28059 declarations, no typechecker errors, 8.4 h) |
| 2026-10-28 | v4 bundle 85c4246d | Lean kernel (v4.36.0-rc1), clean directory | `lake build QueensLean`; axioms of 104 theorems | PASS, standard axioms only |
| 2026-10-28 | v4 bundle 85c4246d | Lean kernel, clean directory | `lake build QueensLeanHeavy`; axioms of 4 theorems | PASS, standard axioms only |
| 2026-10-28 | v4 bundle 85c4246d | leanchecker (toolchain) | 21 modules of QueensLean (import-only roots skipped) | PASS 21/21 |
| 2026-10-23 to 10-28 | same sources | nanoda 0.4.17 | every light theorem, C(10), the 132 C(13) prefix files | PASS |
