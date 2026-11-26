#!/usr/bin/env python3
"""Which values does the gadget miss? Computer algebra behind section 3.1 of DIRECTION.md.

    pip install sympy && python3 scripts/omitted_set.py

With u = 1 + x y: for u != 0, P = a turns Q = b and R = c into the two equations E1, E2 below in
x and u. Their resultant in x is a u^3 (D u^3 + (b^2 - 12 a) u - 4 a); it has no root exactly
when b^2 = 12 a and 3 b c = 4. The cases a = 0, c = 0 and u = 0 always give a preimage. Then spot
checks with Groebner bases: targets on the curve have none, targets off it have one.
A computation, not a proof: the open statement O1 asks for the proof.
"""
import random

import sympy as sp

x, y, z, u, a, b, c = sp.symbols("x y z u a b c")
U = 1 + x * y
P = U**3 * z + y**2 * U * (4 + 3 * x * y)
Q = y + 3 * x * U**2 * z + 3 * x * y**2 * (4 + 3 * x * y)
R = 2 * x - 3 * x**2 * y - x**3 * z

# the two identities that remove y and z
assert sp.expand(x * U * Q - 3 * x**2 * P - U * (U - 1)) == 0
assert sp.expand(R * U**3 - (x * U * (U + 1) - P * x**3)) == 0
E1 = 3 * a * x**2 - b * u * x + u * (u - 1)
E2 = a * x**3 - x * u * (u + 1) + c * u**3
print("resultant in x:", sp.factor(sp.resultant(E1, E2, x)))


def omitted(q):
    return sp.groebner([P - q[0], Q - q[1], R - q[2]], z, y, x, order="lex").exprs == [1]


def on_curve(q):
    return q[1] != 0 and q[0] == q[1] ** 2 / 12 and q[2] == 4 / (3 * q[1])


random.seed(7)
Rat = sp.Rational
rnd = lambda: Rat(random.randint(-9, 9), random.randint(1, 7))
curve = [(t**2 / 12, t, 4 / (3 * t)) for t in [Rat(1), Rat(-1), Rat(2), Rat(-5, 3), Rat(7, 2), Rat(1, 9)]]
off = [(rnd(), rnd(), rnd()) for _ in range(12)]
off += [(0, rnd(), rnd()) for _ in range(3)] + [(rnd(), rnd(), 0) for _ in range(3)]
off += [(0, 0, rnd()), (0, 0, 0), (0, 0, 1)]
off += [(t**2 / 12, t, s) for t, s in [(Rat(2), Rat(1)), (Rat(3), Rat(-2)), (Rat(-1), Rat(5, 3))]]
off += [(r, t, 4 / (3 * t)) for r, t in [(Rat(1), Rat(2)), (Rat(-2, 3), Rat(5)), (Rat(0), Rat(1))]]
off += [(t**2 / 16, t, 0) for t in [Rat(2), Rat(3)]]
off = [q for q in off if not on_curve(q)]
print("on the curve:", len(curve), "targets, all omitted:", all(omitted(q) for q in curve))
print("off the curve:", len(off), "targets, omitted:", [q for q in off if omitted(q)])
