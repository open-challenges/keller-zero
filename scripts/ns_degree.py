#!/usr/bin/env python3
"""The least Nullstellensatz degree of an omitted target of the gadget.

    python3 scripts/ns_degree.py [t ...]        (default: 2 1 -3 5/2)

For the target q = (t^2/12, t, 4/(3t)), which the gadget F never takes, finds the least D for
which 1 = g_1 (F_1 - q_1) + g_2 (F_2 - q_2) + g_3 (F_3 - q_3) with deg(g_i F_i) <= D.
Linear algebra modulo the prime 2^61 - 1: a computation, not a proof.
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import p_add, p_const, p_degree, parse  # noqa: E402

PRIME = 2 ** 61 - 1
HERE = os.path.dirname(os.path.abspath(__file__))
GADGET = json.load(open(os.path.join(HERE, "..", "submissions", "alpoge-stambler", "gadget.json")))


def monomials(n, d):
    if n == 1:
        return [(k,) for k in range(d + 1)]
    return [(k,) + rest for k in range(d + 1) for rest in monomials(n - 1, d - k)]


def one_in_span(polys, d):
    """Is 1 a combination of the products m * f, m a monomial, f in polys, deg(m f) <= d?"""
    n = len(next(iter(polys[0])))
    column = {m: i for i, m in enumerate(monomials(n, d))}
    one = column[(0,) * n]
    pivots = {}
    for f in polys:
        terms = [(e, c.numerator * pow(c.denominator, -1, PRIME) % PRIME) for e, c in f.items()]
        for m in monomials(n, d - p_degree(f)):
            row = {}
            for e, c in terms:
                k = column[tuple(i + j for i, j in zip(e, m))]
                row[k] = (row.get(k, 0) + c) % PRIME
            while True:
                lead = max((k for k, c in row.items() if c and k != one), default=None)
                if lead is None:
                    if row.get(one, 0):
                        return True
                    break
                if lead not in pivots:
                    pivots[lead] = row
                    break
                piv = pivots[lead]
                factor = row[lead] * pow(piv[lead], -1, PRIME) % PRIME
                for k, c in piv.items():
                    row[k] = (row.get(k, 0) - factor * c) % PRIME
                row = {k: c for k, c in row.items() if c}
    return False


def main(args):
    names = GADGET["variables"]
    gadget = [parse(t, names) for t in GADGET["map"]]
    for t in [Fraction(a) for a in (args or ["2", "1", "-3", "5/2"])]:
        target = (t * t / 12, t, 4 / (3 * t))
        polys = [p_add(f, p_const(q, len(names)), -1) for f, q in zip(gadget, target)]
        least = next((d for d in range(max(map(p_degree, polys)), 31) if one_in_span(polys, d)), None)
        print(json.dumps({"t": str(t), "least_degree": least, "modulo": "2^61 - 1"}))


if __name__ == "__main__":
    main(sys.argv[1:])
