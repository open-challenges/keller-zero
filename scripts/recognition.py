#!/usr/bin/env python3
"""Recognising a map with constant Jacobian determinant is polynomial identity testing.

    python3 scripts/recognition.py

Two things, both exact, standard library only.

1. From a product of matrices to a map of degree two. Given matrices A_1 (1 x n_2), A_2, ...,
   A_L (n_L x 1) whose entries are polynomials of degree at most one in x, the 1 x 1 product
   f = A_1 A_2 ... A_L is the general polynomial with a small formula or branching program.
   `quadratic_map` builds a map of degree two in the variables (x, t, y),

       (x, t, y)  ->  (x, t, (I - C(x, t)) y),

   where C carries A_1 .. A_L and the 1 x 1 matrix (t) around a cycle of blocks. Its Jacobian
   determinant is det(I - C) = 1 - t f. So the map has constant Jacobian determinant exactly
   when f is the zero polynomial. The script builds the map for a few products, some of them
   identically zero for a reason that is not visible term by term, and compares its Jacobian
   determinant, computed exactly, with 1 - t f.

2. The test with random points. `looks_constant` evaluates the Jacobian determinant at the
   origin and at random integer points: a map whose Jacobian determinant is constant always
   passes, and one whose determinant is not constant fails each round with probability at least
   1/2 (Schwartz, Zippel). This is the algorithm that puts recognition in coRP.
"""
import json
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import determinant, p_add, p_const, p_degree, p_diff, p_eval, p_mul, parse  # noqa: E402


def quadratic_map(matrices, xnames):
    """The map (x, t, y) -> (x, t, (I - C) y) for the product of `matrices` (lists of rows of
    polynomial texts in xnames). Returns (names, polynomials, f) with f the product."""
    sizes = [len(matrices[0][0])] + [len(a[0]) for a in matrices[1:]]      # n_2 .. n_L, then 1
    assert len(matrices[0]) == 1 and sizes[-1] == 1
    for a, rows in zip(matrices[1:], sizes):
        assert len(a) == rows
    blocks = [1] + sizes[:-1] + [1]            # the block of the start, n_2 .. n_L, the block of t
    start = [sum(blocks[:i]) for i in range(len(blocks))]
    k = sum(blocks)
    names = list(xnames) + ["t"] + ["y%d" % (i + 1) for i in range(k)]
    n = len(names)
    read = lambda text: parse(text, names)
    C = [[{} for _ in range(k)] for _ in range(k)]
    for i, a in enumerate(matrices):           # A_(i+1) sits between block i and block i + 1
        for r, row in enumerate(a):
            for c, text in enumerate(row):
                C[start[i] + r][start[i + 1] + c] = read(text)
    C[start[-1]][0] = read("t")                # and (t) closes the cycle
    ys = [read("y%d" % (i + 1)) for i in range(k)]
    polys = [read(v) for v in xnames] + [read("t")]
    for r in range(k):
        row = ys[r]
        for c in range(k):
            if C[r][c]:
                row = p_add(row, p_mul(C[r][c], ys[c]), -1)
        polys.append(row)
    # the product itself, as a polynomial
    prod = [[read(t) for t in row] for row in matrices[0]]
    for a in matrices[1:]:
        b = [[read(t) for t in row] for row in a]
        prod = [[sum_polys([p_mul(prod[i][l], b[l][j]) for l in range(len(b))]) for j in range(len(b[0]))]
                for i in range(len(prod))]
    return names, polys, prod[0][0]


def sum_polys(ps):
    total = {}
    for p in ps:
        total = p_add(total, p)
    return total


def jacobian_determinant(polys, n):
    return determinant([[p_diff(f, j) for j in range(n)] for f in polys], n)


def number_determinant(rows):
    """Determinant of a square matrix of fractions, by elimination."""
    m = [list(r) for r in rows]
    n, det = len(m), Fraction(1)
    for c in range(n):
        pivot = next((r for r in range(c, n) if m[r][c]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != c:
            m[c], m[pivot] = m[pivot], m[c]
            det = -det
        det *= m[c][c]
        for r in range(c + 1, n):
            if m[r][c]:
                factor = m[r][c] / m[c][c]
                for j in range(c, n):
                    m[r][j] -= factor * m[c][j]
    return det


def looks_constant(polys, n, rounds=8, rng=None):
    """True when the Jacobian determinant is nonzero at the origin and takes the same value at
    `rounds` random points. Never wrong on a map with constant Jacobian determinant."""
    rng = rng or random.Random(0)
    jac = [[p_diff(f, j) for j in range(n)] for f in polys]
    at = lambda point: number_determinant([[p_eval(e, point) for e in row] for row in jac])
    base = at([Fraction(0)] * n)
    if base == 0:
        return False
    bound = 2 * n * max(1, max(p_degree(f) for f in polys))
    return all(at([Fraction(rng.randint(1, bound)) for _ in range(n)]) == base for _ in range(rounds))


CASES = [
    ("x1 x2 - x2 x1, zero", ["x1", "x2"], [[["x1", "x2"]], [["x2"], ["-x1"]]]),
    ("(x1 + x2)^2 - x1^2 - 2 x1 x2 - x2^2, zero", ["x1", "x2"],
     [[["x1 + x2", "x1", "x1", "x2"]], [["x1 + x2"], ["-x1"], ["-2*x2"], ["-x2"]]]),
    ("a 2 x 2 determinant minus itself, zero", ["a", "b", "c", "d"],
     [[["a", "b"]], [["d", "-d"], ["-c", "c"]], [["1"], ["1"]]]),
    ("x1 x2 + 1, not zero", ["x1", "x2"], [[["x1", "1"]], [["x2"], ["1"]]]),
    ("x1 (x2 + x3) x1, not zero", ["x1", "x2", "x3"], [[["x1"]], [["x2 + x3"]], [["x1"]]]),
]


def main():
    ok = True
    for label, xnames, matrices in CASES:
        names, polys, f = quadratic_map(matrices, xnames)
        n = len(names)
        jac = jacobian_determinant(polys, n)
        t = parse("t", names)
        expected = p_add(p_const(1, n), p_mul(t, f), -1)
        agrees = jac == expected
        constant = set(jac) == {(0,) * n}
        random_test = looks_constant(polys, n)
        good = (agrees and constant == (f == {}) and random_test == constant
                and constant == label.endswith(", zero") and max(map(p_degree, polys)) <= 2)
        ok &= good
        print(json.dumps({"product": label, "variables": n, "degree": max(map(p_degree, polys)),
                          "jacobian_is_1_minus_t_f": agrees, "constant_jacobian": constant,
                          "random_test_says_constant": random_test}))
    print(json.dumps({"ok": ok}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
