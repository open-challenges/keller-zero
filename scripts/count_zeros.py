#!/usr/bin/env python3
"""Counting the zeros of the map of the reduction counts satisfying assignments.

    python3 scripts/count_zeros.py

For a 3CNF formula with n variables and m clauses, the map of the reduction (at degree 3 here)
has exactly

    3^m * (sum over satisfying assignments of 2^(number of true variables))

zeros: a true variable has two points, a false one has one, and every clause block has three.
Adding to each variable x a twin y with the clauses (x or y) and (not x or not y) makes every
satisfying assignment set exactly n variables true, so the map of the new formula has

    2^n * 3^(m + 2n) * (number of satisfying assignments of the old one)

zeros. The script counts zeros by trying the three points of every block (by `H_eq_zero_iff`
in lean/KellerZero/Gadget.lean there are no other candidates) and compares.
"""
import itertools
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import p_eval  # noqa: E402
from lower_degree import formula  # noqa: E402

POINTS = [(0, 0, Fraction(-1, 4)), (1, Fraction(-3, 2), Fraction(13, 2)), (-1, Fraction(3, 2), Fraction(13, 2))]


def zeros(clauses):
    L, coords, n, m = formula(clauses)
    count = 0
    for choice in itertools.product(range(3), repeat=n + m):
        point = L.above([v for k in choice for v in POINTS[k]])
        count += all(p_eval(f.terms, point) == 0 for f in coords)
    return count, n, m


def assignments(clauses, n):
    """(number of satisfying assignments, the same with weight 2 per true variable)."""
    plain = weighted = 0
    for bits in itertools.product([False, True], repeat=n):
        if all(any(bits[abs(l) - 1] == (l > 0) for l in c) for c in clauses):
            plain += 1
            weighted += 2 ** sum(bits)
    return plain, weighted


def twins(clauses, n):
    """Every variable k gets the twin n + k, forced to be its negation."""
    return list(clauses) + [c for k in range(1, n + 1) for c in ((k, n + k, n + k), (-k, -(n + k), -(n + k)))]


def main():
    ok = True
    for clauses in ([(1, 1, 1)], [(1, 2, 2), (-1, -2, -2)], [(1, 1, 2), (-1, 2, 2)],
                    [(1, 2, 2), (-1, -2, -2), (1, -2, -2)]):
        count, n, m = zeros(clauses)
        plain, weighted = assignments(clauses, n)
        good = count == 3 ** m * weighted
        ok &= good
        print(json.dumps({"formula": clauses, "zeros": count, "predicted": 3 ** m * weighted, "agrees": good}))
    clauses, n = [(1, 1, 1)], 1
    count, n2, m2 = zeros(twins(clauses, n))
    plain, _ = assignments(clauses, n)
    good = count == 2 ** n * 3 ** m2 * plain
    ok &= good
    print(json.dumps({"formula": clauses, "with_twins": twins(clauses, n), "zeros": count,
                      "predicted": 2 ** n * 3 ** m2 * plain, "satisfying_assignments": plain, "agrees": good}))
    print(json.dumps({"ok": ok}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
