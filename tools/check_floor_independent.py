"""Second, independent check of the Lean floor families: rebuild each family board from families.json-style run data
(construct_gen.family), then count flat legality and toroidal conflict pairs directly with numpy (no Monsky code)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, construct_gen as g, json
from math import gcd
CL = [(12, 2), (12, 10), (12, 3), (12, 9), (12, 4), (24, 6), (24, 18), (24, 8), (24, 20), (12, 0)]
bad = 0; tested = 0
for P, r in CL:
    for s in range(2 if r % 2 else 3):
        f = g.family(P, r, s)
        for u in range(0, 14):
            n = f["M"] * u + f["n0"]; xs = []; ys = []
            for j, ((xa, xb), (ya, yb), (la, lb)) in enumerate(f["runs"]):
                for k in range(la * u + lb):
                    xs.append(xa * u + xb + f["steps"][j][0] * k); ys.append(ya * u + yb + f["steps"][j][1] * k)
            x = np.array(xs); y = np.array(ys)
            legal = len(x) == n and len(set(x)) == n and len(set(y)) == n and len(set(x + y)) == n and len(set(x - y)) == n
            c = sum(int(v * (v - 1) // 2) for fam in ((x + y) % n, (x - y) % n) for v in np.bincount(fam, minlength=n))
            want = 0 if n % 6 in (1, 5) else (3 if n % 6 == 0 else 2)
            tested += 1
            if not (legal and c == want): bad += 1; print("FAIL", n, legal, c, want)
print(f"{tested} family boards checked (n up to {max(72*13+92, 0)}), failures {bad}")
