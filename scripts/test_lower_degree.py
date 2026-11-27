#!/usr/bin/env python3
"""Tests of lower_degree.py: python3 scripts/test_lower_degree.py"""
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import check, determinant, p_diff, p_eval  # noqa: E402
from lower_degree import WIRES, formula, gadget  # noqa: E402


def main():
    # the gadget at every degree: exact Jacobian determinant -2, two points with one value
    for degree in (6, 5, 4, 3, "eleven", "twelve"):
        v = check(gadget(degree))
        want = degree if isinstance(degree, int) else 3
        assert v["ok"] and v["degree"] == want and v["variables"] == 3 + WIRES[degree] and v["jacobian"] == "-2", v
        assert v["value"][:3] == ["-1/4", "0", "0"] and set(v["value"][3:]) == {"0"}, v
        print("gadget: degree %d in %d variables" % (want, v["variables"]))
    # the map of the reduction at degree 3; x1 false, x2 true satisfies the first formula
    r0, r1 = (0, 0, Fraction(-1, 4)), (1, Fraction(-3, 2), Fraction(13, 2))
    for clauses, good, bad in [([(1, 1, 2), (-1, 2, 2)], r0 + r1, r1 + r0),
                               ([(1, 2, 2), (-1, -2, -2), (1, -2, -2)], r1 + r0, r1 + r1)]:
        start = time.time()
        L, coords, n, m = formula(clauses)
        N = len(L.ring.names)
        assert N == 10 * n + 13 * m and all(c.degree() <= 3 for c in coords)
        jac = determinant([[p_diff(c.terms, j) for j in range(N)] for c in coords], N)
        assert jac == {(0,) * N: Fraction(-3456) ** (n + m)}, jac
        # a satisfying assignment gives a zero (witness blocks at the point with x = 0) ...
        point = L.above(list(good) + list(r0) * m)
        assert all(p_eval(c.terms, point) == 0 for c in coords)
        # ... and a falsifying one does not, at any of the 3^m choices of witness blocks
        for pick in range(3 ** m):
            ws = [((0, 0, Fraction(-1, 4)), r1, (-1, Fraction(3, 2), Fraction(13, 2)))[(pick // 3 ** j) % 3] for j in range(m)]
            point = L.above(list(bad) + [v for w in ws for v in w])
            assert any(p_eval(c.terms, point) != 0 for c in coords)
        print("formula %s: degree 3 in %d variables, Jacobian determinant (-3456)^%d, %.1f s"
              % (clauses, N, n + m, time.time() - start))
    print("ok")


if __name__ == "__main__":
    main()
