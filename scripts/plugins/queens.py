"""leankit plugin for the queens papers: an independent Python version of the plain definitions in Spec.lean.
A board is a list b: row i has its queen in column b[i]. Written from the chess meaning, not from the Lean code."""


def is_solution(b):
    n = len(b)
    return all(b[i] != b[j] and abs(i - j) != abs(b[i] - b[j]) for i in range(n) for j in range(i + 1, n))


def conflicts(b):
    """Pairs of queens on a common wrapped sum diagonal plus pairs on a common wrapped difference diagonal."""
    n = len(b)
    s = sum(1 for i in range(n) for j in range(i + 1, n) if (i + b[i]) % n == (j + b[j]) % n)
    d = sum(1 for i in range(n) for j in range(i + 1, n) if (i - b[i]) % n == (j - b[j]) % n)
    return s + d


PREDICATES = {"IsSolution": is_solution}
FUNCTIONS = {"confSpec": conflicts}
