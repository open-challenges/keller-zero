#!/usr/bin/env python3
"""A short witness that a map with constant Jacobian determinant has a complex zero.

    python3 scripts/witness.py

The witness is a prime p and a point a with coordinates modulo p such that

    F(a) = 0 (mod p)    and    det JF(a) != 0 (mod p).

`verify` checks one in polynomial time: it evaluates the polynomials and one determinant of
numbers modulo p. No determinant of polynomials is expanded.

Why it proves something: by Hensel's lemma such a point lifts to a zero of F with p-adic
coordinates, so the equations F = 0 have a solution in a field of characteristic zero, and then
(Hilbert's Nullstellensatz) a complex one. This holds for every square system; nothing is
assumed about F.

Why a witness exists when F has constant Jacobian determinant c and a complex zero: every zero
modulo a prime that does not divide c passes the second test, and under the generalized Riemann
hypothesis there is a prime with polynomially many digits modulo which F has a zero (Koiran,
1996). COMPLEXITY.md has the statement. Without the hypothesis the prime may be long; the check
is the same.

The examples: the map of the reduction of a satisfiable formula at degree 3; a map of degree 2
in 40 variables whose only zero has a coordinate of 2^39 binary digits; and the gadget over a
target with one rational preimage and two complex ones.
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import p_diff, parse  # noqa: E402
from lower_degree import GADGET, formula  # noqa: E402


def is_prime(p):
    if p < 2:
        return False
    k = 2
    while k * k <= p:
        if p % k == 0:
            return False
        k += 1
    return True


def reduce(c, p):
    c = Fraction(c)
    if c.denominator % p == 0:
        raise ValueError("a coefficient has denominator divisible by %d" % p)
    return c.numerator * pow(c.denominator, -1, p) % p


def evaluate(poly, a, p):
    total = 0
    for e, c in poly.items():
        term = reduce(c, p)
        for x, k in zip(a, e):
            if k:
                term = term * pow(x, k, p) % p
        total = (total + term) % p
    return total


def determinant_mod(rows, p):
    m = [list(r) for r in rows]
    n, det = len(m), 1
    for c in range(n):
        pivot = next((r for r in range(c, n) if m[r][c]), None)
        if pivot is None:
            return 0
        if pivot != c:
            m[c], m[pivot] = m[pivot], m[c]
            det = -det
        det = det * m[c][c] % p
        inv = pow(m[c][c], -1, p)
        for r in range(c + 1, n):
            if m[r][c]:
                factor = m[r][c] * inv % p
                for j in range(c, n):
                    m[r][j] = (m[r][j] - factor * m[c][j]) % p
    return det % p


def verify(polys, p, a):
    """Is (p, a) a witness that the square system polys = 0 has a complex solution?"""
    n = len(polys)
    if not is_prime(p) or len(a) != n:
        return False
    a = [x % p for x in a]
    if any(evaluate(f, a, p) for f in polys):
        return False
    jac = [[evaluate(p_diff(f, j), a, p) for j in range(n)] for f in polys]
    return determinant_mod(jac, p) != 0


def main():
    ok = True
    # 1. the reduction at degree 3: x1 false, x2 true satisfies (x1 or x1 or x2) and (not x1 or x2 or x2)
    L, coords, n, m = formula([(1, 1, 2), (-1, 2, 2)])
    r0, r1 = (0, 0, Fraction(-1, 4)), (1, Fraction(-3, 2), Fraction(13, 2))
    zero = L.above(list(r0 + r1) + list(r0) * m)
    polys = [c.terms for c in coords]
    p = 5
    a = [reduce(v, p) for v in zero]
    good = verify(polys, p, a) and not verify(polys, p, [(v + 1) % p for v in a])
    ok &= good
    print(json.dumps({"example": "the map of a satisfiable formula at degree 3", "variables": len(polys),
                      "prime": p, "witness_accepted": good}))
    # 2. x1 = 2, x(k+1) = x(k)^2: one zero, with coordinates 2^(2^k)
    N = 40
    names = ["x%d" % (i + 1) for i in range(N)]
    polys = [parse("x1 - 2", names)] + [parse("x%d - x%d^2" % (i + 1, i), names) for i in range(1, N)]
    p = 5
    a = [2]
    for _ in range(N - 1):
        a.append(a[-1] * a[-1] % p)
    good = verify(polys, p, a)
    ok &= good
    print(json.dumps({"example": "repeated squaring, degree 2", "variables": N,
                      "binary_digits_of_the_last_coordinate_of_the_zero": 2 ** (N - 1) + 1,
                      "prime": p, "witness_accepted": good}))
    # 3. the gadget over (1, 1, 1): its cubic is (m - 2)(m^2 + 1)
    names = ["x", "y", "z"]
    polys = [parse("(%s) - 1" % g, names) for g in GADGET]
    counts = {}
    for p in (5, 7, 11, 13, 17):
        count = sum(verify(polys, p, (x, y, z)) for x in range(p) for y in range(p) for z in range(p))
        counts[p] = count
    good = counts == {5: 1, 7: 1, 11: 1, 13: 3, 17: 3}       # -1 is a square modulo 13 and 17 only; 5 divides the discriminant
    ok &= good
    print(json.dumps({"example": "the gadget over (1, 1, 1): one rational preimage, two complex",
                      "witnesses_modulo_p": counts, "as_expected": good}))
    # 4. and none over the omitted target, modulo any of these primes
    polys = [parse("12*(%s) + 3 - 7" % GADGET[0], names), parse("12*(%s) - 24" % GADGET[1], names),
             parse("12*(%s) - 8" % GADGET[2], names)]
    none = not any(all(evaluate(f, (x, y, z), p) == 0 for f in polys)
                   for p in (5, 7, 11, 13) for x in range(p) for y in range(p) for z in range(p))
    ok &= none
    print(json.dumps({"example": "the gadget over the omitted target (7, 24, 8)",
                      "no_zero_modulo": [5, 7, 11, 13], "holds": none}))
    print(json.dumps({"ok": ok}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
