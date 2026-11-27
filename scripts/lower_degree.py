#!/usr/bin/env python3
"""Lower the degree of a map with constant Jacobian determinant by adding variables.

    python3 scripts/lower_degree.py gadget 3          # the gadget at degree 3 (11 variables)
    python3 scripts/lower_degree.py gadget 4|5|6      # 7, 6 and 5 variables
    python3 scripts/lower_degree.py gadget twelve     # an earlier degree 3, with 12 variables
    python3 scripts/lower_degree.py formula "1 2 3, -1 -2 -3"   # the map of the reduction at degree 3

Prints a gadget.json. `formula` takes clauses of three literals, variable k as k and its
negation as -k.

The method is the reduction of Bass, Connell and Wright (1982), done with shared wires. Given a
map F in the variables x, add variables t_1 .. t_r and build, in order,

    wire_i = t_i + l_i(x, t_1 .. t_(i-1)) + q_i(wire_1 .. wire_(i-1)),

then output G = ( F_j(x) - p_j(wires),  t_i + l_i ). With S(x, t) = (x, wires) and
T(a, w) = (a - p(w), w_i - q_i(w)), both triangular and so invertible with Jacobian
determinant 1, G = T o (F x id) o S. Hence det JG = det JF. The equations "t_i + l_i = 0" have
exactly one solution t above every x, and there the wires take fixed values w* (w*_i =
q_i(w*), from the first wire on). p is chosen with p(w*) = 0, so G(x, t) = (a, 0) exactly when
F(x) = a and t is that solution: G has the fibres of F, point for point.

The choice of l, q and p is what keeps every coordinate of G within the degree: it is made by
hand below, and the degree of the result is asserted, not assumed.

The eight wires used at degree 3 are those of the eleven-variable map published on 20 July 2026
(gist Spacerat/08b4a43f6b6ca57178efabc220170ce8), in the order d, a, b, c, h, k, q, s; the same
map is `cubic11Map` in lean/KellerZero/Cubic11.lean. The wires at degrees 4, 5, 6 and the
nine-wire variant `twelve` were found for this repository.
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import p_add, p_const, p_degree, p_mul, parse, show  # noqa: E402


class Poly:
    """A polynomial with rational coefficients in the variables of its ring."""

    def __init__(self, ring, terms):
        self.ring, self.terms = ring, terms

    def _lift(self, other):
        return other if isinstance(other, Poly) else Poly(self.ring, p_const(Fraction(other), len(self.ring.names)))

    def __add__(self, other):
        return Poly(self.ring, p_add(self.terms, self._lift(other).terms))

    __radd__ = __add__

    def __sub__(self, other):
        return Poly(self.ring, p_add(self.terms, self._lift(other).terms, -1))

    def __rsub__(self, other):
        return self._lift(other) - self

    def __neg__(self):
        return self._lift(0) - self

    def __mul__(self, other):
        return Poly(self.ring, p_mul(self.terms, self._lift(other).terms))

    __rmul__ = __mul__

    def __pow__(self, k):
        out = self._lift(1)
        for _ in range(k):
            out = out * self
        return out

    def degree(self):
        return p_degree(self.terms)

    def uses(self):
        """Indices of the variables that occur."""
        return {i for e in self.terms for i, k in enumerate(e) if k}

    def text(self):
        out = []
        for e, c in sorted(self.terms.items(), key=lambda ec: (-sum(ec[0]), ec[0])):
            mono = "*".join(n if k == 1 else "%s^%d" % (n, k) for n, k in zip(self.ring.names, e) if k)
            mag = abs(c)
            coef = "" if (mag == 1 and mono) else (show(mag) if mag.denominator == 1 else "%d/%d" % (mag.numerator, mag.denominator))
            body = mono if not coef else (coef if not mono else (coef + "*" + mono))
            out.append(("- " if c < 0 else "+ ") + body)
        s = " ".join(out) if out else "0"
        return s[2:] if s.startswith("+ ") else "-" + s[2:]


class Ring:
    def __init__(self, names):
        self.names = list(names)

    def var(self, name):
        i = self.names.index(name)
        n = len(self.names)
        return Poly(self, {(0,) * i + (1,) + (0,) * (n - i - 1): Fraction(1)})

    def read(self, text):
        return Poly(self, parse(text, self.names))


class Lowering:
    """Builds G from F wire by wire; see the module text. `count` is the number of new
    variables, fixed at the start so that all polynomials live in one ring."""

    def __init__(self, xnames, count):
        self.ring = Ring(list(xnames) + ["t%d" % (i + 1) for i in range(count)])
        self.nx, self.count = len(xnames), count
        self.t = [self.ring.var("t%d" % (i + 1)) for i in range(count)]
        self.wires, self.outputs = [], []

    def wire(self, ell, q=None):
        """A new wire t + ell + q, where ell uses only x and earlier t, and q is built from
        earlier wires (the caller passes a polynomial in them, already multiplied out)."""
        i = len(self.wires)
        if i >= self.count:
            raise ValueError("more wires than variables set aside")
        ell = self.ring.read(ell) if isinstance(ell, str) else ell
        if any(v >= self.nx + i for v in ell.uses()):
            raise ValueError("wire %d: its own part may use only x and earlier t" % (i + 1))
        w = self.t[i] + ell + (q if q is not None else 0)
        self.wires.append(w)
        self.outputs.append(self.t[i] + ell)
        return w

    def finish(self, mains, bound):
        if len(self.wires) != self.count:
            raise ValueError("%d variables set aside, %d wires built" % (self.count, len(self.wires)))
        coords = list(mains) + self.outputs
        worst = max(c.degree() for c in coords)
        if worst > bound:
            raise ValueError("degree %d, wanted at most %d: %s" % (worst, bound, [c.degree() for c in coords]))
        return coords

    def above(self, xvalues):
        """The point above x at which every added coordinate t_i + l_i is zero."""
        vals = [Fraction(v) for v in xvalues]
        for out in self.outputs:
            i = len(vals)
            rest = Fraction(0)
            for e, c in out.terms.items():
                if e[i]:
                    continue                      # the term t_i itself
                term = c
                for x, k in zip(vals, e):
                    term *= x ** k
                rest += term
            vals.append(-rest)
        return vals


# The gadget (Alpöge's map, as in Stambler's reduction), with u = 1 + x y:
#   E = u z + 3 y^2,   P = u^2 E + u y^2,   Q = y + 3 x y^2 + 3 (x u) E,   R = 2 x - 3 x^2 y - x^3 z.
GADGET = ["(1 + x*y)^3*z + y^2*(1 + x*y)*(4 + 3*x*y)",
          "y + 3*x*(1 + x*y)^2*z + 3*x*y^2*(4 + 3*x*y)",
          "2*x - 3*x^2*y - x^3*z"]
FIBRE = [("0", "0", "-1/4"), ("1", "-3/2", "13/2")]      # two points with the value (-1/4, 0, 0)


def gadget_wires(L, x, y, z, degree):
    """Wires for one copy of the gadget in the variables named x, y, z of the ring of L.
    Returns the three reduced coordinates (P, Q, R minus what the wires carry) and the wire
    that carries x^2 at degree 3 (the reduction of a formula uses it), else None."""
    r = L.ring
    X, Y, Z = r.var(x), r.var(y), r.var(z)
    sub = lambda text: text.replace("x", "\0").replace("y", "\1").replace("z", "\2").replace("\0", x).replace("\1", y).replace("\2", z)
    P, Q, R = (r.read(sub(g)) for g in GADGET)
    u = 1 + X * Y
    E = u * Z + 3 * Y ** 2
    assert (P - (u ** 2 * E + u * Y ** 2)).terms == {} and (Q - (Y + 3 * X * Y ** 2 + 3 * X * u * E)).terms == {}
    k = len(L.wires)
    t = lambda i: L.t[k + i]
    if degree == 7:
        return [P, Q, R], None
    if degree == 6:
        # P = A + (x y) A with A = u E + y^2 of degree 5: one product of two wires.
        A = u * E + Y ** 2
        a = L.wire(X * Y)
        kA = L.wire(A)
        return [P - a * kA, Q, R], None
    if degree == 5:
        # P = E + (u^2 - 1) E + u y^2 and Q = y + 3 x y^2 + 3 (x u) E: two products with E.
        kE = L.wire(E)
        ku = L.wire(2 * X * Y + X ** 2 * Y ** 2)
        kX = L.wire(X * u)
        return [P - ku * kE, Q - 3 * kX * kE, R], None
    if degree == 4:
        # Q through (x u)(E). P = E + (u^2 - 1) E + u y^2: the product leaves t_E x^2 y^2 behind,
        # which (t_E y)(x u) = t_E x y + t_E x^2 y^2 removes.
        kX = L.wire(X * u)
        kE = L.wire(E)
        ku = L.wire(2 * X * Y + X ** 2 * Y ** 2)
        m = L.wire(t(1) * Y)
        return [P - ku * kE + m * kX, Q - 3 * kX * kE, R], None
    if degree == 3:
        d = L.wire(-X * Y)                                   # t1 - x y
        a = L.wire(-t(0) ** 2 + 2 * t(0) * X * Y)            # with the square of d: t2 + x^2 y^2
        b = L.wire(3 * X ** 2 * Y)                           # t3 + 3 x^2 y
        c = L.wire(X * Y * Z + 3 * Y ** 2 + 2 * Z)           # t4 + E + z
        h = L.wire(-X ** 2)                                  # t5 - x^2
        kz = L.wire(X * Z)                                   # t6 + x z
        q = L.wire(t(2) * Z + 3 * t(3) * X)                  # t7: what Q's products leave
        s = L.wire(t(1) * Z + t(3) * X * Y - X * Y * Z - 7 * Y ** 2 + t(3) * t(0) - t(0) * Z)   # t8: P's
        assert (a + d * d - (t(1) + X ** 2 * Y ** 2)).terms == {}
        newP = P - (a * c + c * d * d + d * s)
        newQ = Q - (b * c + d * q)
        newR = R - h * kz
        return [newP, newQ, newR], h
    if degree == "twelve":
        a = L.wire(X * Y)                                    # t1: x y
        kX = L.wire(X * u)                                   # t2: x u
        kE = L.wire(E)                                       # t3: E
        l1 = L.wire(3 * t(1) * Z + 3 * t(2) * X)             # t4: what Q's product leaves, over x y
        a2 = L.wire(-(2 * t(0) * X * Y + t(0) ** 2), a * a)  # t5: exactly t5 + x^2 y^2
        m = L.wire(t(2) * X * Y)                             # t6: t_E x y
        # t7: what P's products leave, over x y; its y^2 also removes the x y^3 of u y^2
        l2 = L.wire(2 * t(0) * Z + t(4) * Z - t(0) * t(2) - Y ** 2)
        c = L.wire(X ** 2)                                   # t8: x^2
        b = L.wire(X * Z)                                    # t9: x z
        assert (a2 - (t(4) + X ** 2 * Y ** 2)).terms == {}
        newP = P - 2 * a * kE - a2 * kE + a * m + a * l2
        newQ = Q - 3 * kX * kE + a * l1
        newR = R + c * b
        return [newP, newQ, newR], c
    raise ValueError("degree 3 to 7")


WIRES = {7: 0, 6: 2, 5: 3, 4: 4, 3: 8, "twelve": 9}


def gadget(degree):
    L = Lowering(["x", "y", "z"], WIRES[degree])
    mains, _ = gadget_wires(L, "x", "y", "z", degree)
    coords = L.finish(mains, 3 if degree == "twelve" else degree)
    points = [L.above(p) for p in FIBRE]
    return {"variables": L.ring.names, "map": [c.text() for c in coords],
            "points": [[show(v) for v in p] for p in points]}


def formula(clauses):
    """The map of Stambler's reduction for a 3CNF formula, at degree 3. Blocks: three variables
    and a gadget's eight wires for every variable of the formula and for every clause; three
    more wires per clause for the product of its three literal values. 11 n + 14 m in all.
    The same map is `cubicReduction` in lean/KellerZero/CubicReduction.lean."""
    n = max(abs(l) for c in clauses for l in c)
    m = len(clauses)
    xn = ["w%d%s" % (i + 1, s) for i in range(n) for s in "xyz"] + ["v%d%s" % (j + 1, s) for j in range(m) for s in "xyz"]
    L = Lowering(xn, 8 * (n + m) + 3 * m)
    mains, squares = [], []
    for i in range(n):
        g, h = gadget_wires(L, "w%dx" % (i + 1), "w%dy" % (i + 1), "w%dz" % (i + 1), 3)
        squares.append((h, L.t[len(L.wires) - 4], L.ring.var("w%dx" % (i + 1)) ** 2))   # the wire t - x^2, its t, x^2
        mains += [12 * g[0] + 3, 12 * g[1], 12 * g[2]]
    delta = [7, 24, 8]
    for j, clause in enumerate(clauses):
        g, _ = gadget_wires(L, "v%dx" % (j + 1), "v%dy" % (j + 1), "v%dz" % (j + 1), 3)
        # literal k is false exactly when f_k = 1 ... the clause fails when f1 f2 f3 = 1, where
        # f = 1 - x^2 for a positive literal and x^2 for a negative one.
        F, f, e, tv = [], [], [], []
        for lit in clause:
            wire, tvar, sq = squares[abs(lit) - 1]
            F.append(1 + wire if lit > 0 else -wire)         # in terms of the wire
            f.append(1 - sq if lit > 0 else sq)              # the polynomial it carries
            e.append(1 if lit > 0 else -1)                   # F = f + e t
            tv.append(tvar)
        base = len(L.wires)
        g12 = L.wire(-(e[0] * tv[0] * f[1] + e[1] * tv[1] * f[0] + e[0] * e[1] * tv[0] * tv[1]), F[0] * F[1])   # t + f1 f2
        assert (g12 - (L.t[base] + f[0] * f[1])).terms == {}
        h = L.wire(e[2] * tv[2] * f[0])                      # carries e3 t3 f1
        k = L.wire(e[1] * e[2] * tv[1] * tv[2])              # carries e2 e3 t2 t3
        prod = g12 * F[2] - h * F[1] + k * F[0]              # = f1 f2 f3 + (degree at most 3)
        assert (prod - f[0] * f[1] * f[2]).degree() <= 3
        # At the fixed wire values the square wires are 0, so F is 1 for a positive literal and
        # 0 for a negative one, and prod is 1 exactly when all three literals are positive.
        fixed = 1 if all(lit > 0 for lit in clause) else 0
        rest = f[0] * f[1] * f[2] - prod + fixed             # degree at most 3
        mains += [12 * g[0] + 3 - delta[0] * rest, 12 * g[1] - delta[1] * rest, 12 * g[2] - delta[2] * rest]
    # the coordinates are listed variable blocks first, as in `mains`; their order does not matter
    coords = L.finish(mains, 3)
    return L, coords, n, m


def main(argv):
    if len(argv) == 2 and argv[0] == "gadget" and argv[1] in ("3", "4", "5", "6", "twelve"):
        print(json.dumps(gadget(argv[1] if argv[1] == "twelve" else int(argv[1])), indent=2))
        return 0
    if len(argv) == 2 and argv[0] == "formula":
        clauses = [tuple(int(l) for l in c.split()) for c in argv[1].split(",")]
        if not clauses or any(len(c) != 3 or 0 in c for c in clauses):
            print("clauses of three nonzero literals, separated by commas", file=sys.stderr)
            return 2
        L, coords, n, m = formula(clauses)
        print(json.dumps({"variables": L.ring.names, "map": [c.text() for c in coords],
                          "formula": clauses, "blocks": {"variables": n, "clauses": m}}, indent=2))
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
