#!/usr/bin/env python3
"""Nullstellensatz certificates for the gadget, and how they move between a formula and its map.

    python3 scripts/certificates.py

Exact rational arithmetic, standard library only. Prints one JSON line per check; exit code 0
when every check passes.

1. The gadget. With H = (12 P + 3, 12 Q, 12 R): the least degree D at which the ideal of H
   contains x^3 - x, 2 y + 3 x, 4 z + 1 - 27 x^2 and x^4 - x^2 with products of degree at most D,
   and the least degree at which 1 is a combination of H - (7, 24, 8). The multipliers found are
   the ones proved in lean/KellerZero/Certificates.lean.
2. The curve. One identity, uniform in t, that puts 4 t in the ideal of the equations of a
   point of the omitted curve.
3. Transfer, on the unsatisfiable formula (x) and (not x). A refutation of the formula of degree
   3 is turned into a refutation of its map K of degree at most 2 * 3 + 18, and that one is
   turned back, by substituting a point for every block, into a refutation of the formula of no
   larger degree. COMPLEXITY.md proves both steps for every formula.
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import p_add, p_const, p_degree, p_mul, p_pow, parse  # noqa: E402

PRIME = 2 ** 61 - 1
P_TEXT = "(1 + x*y)^3*z + y^2*(1 + x*y)*(4 + 3*x*y)"
Q_TEXT = "y + 3*x*(1 + x*y)^2*z + 3*x*y^2*(4 + 3*x*y)"
R_TEXT = "2*x - 3*x^2*y - x^3*z"
TARGET = (7, 24, 8)


def monomials(n, d):
    if n == 1:
        return [(k,) for k in range(d + 1)]
    return [(k,) + rest for k in range(d + 1) for rest in monomials(n - 1, d - k)]


def shift(f, m):
    return {tuple(i + j for i, j in zip(e, m)): c for e, c in f.items()}


def member_mod(polys, target, d):
    """Is target a combination of the products m * f of degree at most d? Modulo PRIME."""
    def red(c):
        return c.numerator * pow(c.denominator, -1, PRIME) % PRIME
    pivots = {}

    def reduce(row):
        while row:
            lead = max(row)
            if lead not in pivots:
                return row
            piv = pivots[lead]
            factor = row[lead] * pow(piv[lead], -1, PRIME) % PRIME
            for k, c in piv.items():
                v = (row.get(k, 0) - factor * c) % PRIME
                if v:
                    row[k] = v
                else:
                    row.pop(k, None)
        return row
    n = len(next(iter(polys[0])))
    for f in polys:
        ff = {e: red(c) for e, c in f.items()}
        for m in monomials(n, d - p_degree(f)):
            row = reduce(shift(ff, m))
            if row:
                pivots[max(row)] = row
    return not reduce({e: red(c) for e, c in target.items()})


def member_exact(polys, target, d):
    """Multipliers g with sum g_k f_k = target and deg(g_k f_k) <= d, or None. Exact."""
    n = len(next(iter(polys[0])))
    pivots = {}

    def reduce(row, tag):
        while row:
            lead = max(row)
            if lead not in pivots:
                return row, tag
            prow, ptag = pivots[lead]
            factor = row[lead] / prow[lead]
            for k, c in prow.items():
                v = row.get(k, 0) - factor * c
                if v:
                    row[k] = v
                else:
                    row.pop(k, None)
            for k, c in ptag.items():
                v = tag.get(k, 0) - factor * c
                if v:
                    tag[k] = v
                else:
                    tag.pop(k, None)
        return row, tag
    for i, f in enumerate(polys):
        for m in monomials(n, d - p_degree(f)):
            row, tag = reduce(shift(f, m), {(i, m): Fraction(1)})
            if row:
                pivots[max(row)] = (row, tag)
    row, tag = reduce(dict(target), {})
    if row:
        return None
    gs = [dict() for _ in polys]
    for (i, m), c in tag.items():
        gs[i][m] = -c
    return gs


def least_degree(polys, target, hi=20):
    lo = max(max(map(p_degree, polys)), p_degree(target))
    return next((d for d in range(lo, hi + 1) if member_mod(polys, target, d)), None)


def combine(polys, gs):
    total = {}
    for f, g in zip(polys, gs):
        if g:
            total = p_add(total, p_mul(f, g))
    return total


def substitute(p, images, n_out):
    """p with variable i replaced by the polynomial images[i] (in n_out variables)."""
    total = {}
    for e, c in p.items():
        term = p_const(c, n_out)
        for i, k in enumerate(e):
            if k:
                term = p_mul(term, p_pow(images[i], k, n_out))
        total = p_add(total, term)
    return total


def gadget_checks():
    names = ["x", "y", "z"]
    H = [parse("12*(%s) + 3" % P_TEXT, names), parse("12*(%s)" % Q_TEXT, names), parse("12*(%s)" % R_TEXT, names)]
    out, ok = [], True
    for text in ["x^3 - x", "2*y + 3*x", "4*z + 1 - 27*x^2", "x^4 - x^2"]:
        t = parse(text, names)
        d = least_degree(H, t)
        gs = member_exact(H, t, d)
        good = gs is not None and p_add(combine(H, gs), t, -1) == {}
        ok &= good
        out.append({"check": "in the ideal of H", "polynomial": text, "least_degree": d, "exact": good})
    shifted = [p_add(h, p_const(c, 3), -1) for h, c in zip(H, TARGET)]
    one = p_const(1, 3)
    d = least_degree(shifted, one)
    gs = member_exact(shifted, one, d)
    good = gs is not None and p_add(combine(shifted, gs), one, -1) == {}
    ok &= good
    out.append({"check": "1 in the ideal of H - (7, 24, 8)", "least_degree": d, "exact": good})
    return out, ok


def curve_check():
    names = ["x", "y", "z", "t"]
    eqs = [parse("12*(%s) - t^2" % P_TEXT, names), parse("(%s) - t" % Q_TEXT, names), parse("3*t*(%s) - 4" % R_TEXT, names)]
    gs = [parse("x*(2*(1 + x*y) - t*x)", names),
          parse("t^2*x^2 + 2*t*x*(x*y + 2) - 8*(1 + x*y)^2", names),
          parse("(t - 2*y)*(1 + x*y)^2", names)]
    good = p_add(combine(eqs, gs), parse("4*t", names), -1) == {}
    degree = max(sum(e[:3]) for f, g in zip(eqs, gs) for e in p_mul(f, g))
    return [{"check": "4 t in the ideal of the curve equations, for every t", "degree_in_xyz": degree, "exact": good}], good


def transfer_check():
    """The formula (x) and (not x): one variable block z = (x, y, z), two clause blocks u, v."""
    names = ["x", "y", "z", "u1", "u2", "u3", "v1", "v2", "v3"]
    n = len(names)

    def H(a, b, c):
        s = lambda t: t.replace("x", "\0").replace("y", "\1").replace("z", "\2").replace("\0", a).replace("\1", b).replace("\2", c)
        return [parse("12*(%s) + 3" % s(P_TEXT), names), parse("12*(%s)" % s(Q_TEXT), names), parse("12*(%s)" % s(R_TEXT), names)]
    Hz, Hu, Hv = H("x", "y", "z"), H("u1", "u2", "u3"), H("v1", "v2", "v3")
    f1 = parse("(1 - x^2)^3", names)          # the clause (x or x or x) is false when x^2 = 0
    f2 = parse("x^6", names)                  # the clause (not x ...) is false when x^2 = 1
    K = Hz + [p_add(h, p_mul(p_const(d, n), f1), -1) for h, d in zip(Hu, TARGET)] \
           + [p_add(h, p_mul(p_const(d, n), f2), -1) for h, d in zip(Hv, TARGET)]
    # pieces, found in three variables and placed in the right block
    three = ["x", "y", "z"]
    H3 = [parse("12*(%s) + 3" % P_TEXT, three), parse("12*(%s)" % Q_TEXT, three), parse("12*(%s)" % R_TEXT, three)]
    quartic = parse("x^4 - x^2", three)
    cq = member_exact(H3, quartic, least_degree(H3, quartic))
    shifted = [p_add(h, p_const(c, 3), -1) for h, c in zip(H3, TARGET)]
    g = member_exact(shifted, p_const(1, 3), least_degree(shifted, p_const(1, 3)))

    def place(p, offset):
        return {(0,) * offset + e + (0,) * (n - offset - 3): c for e, c in p.items()}
    cz = [place(c, 0) for c in cq]                                   # sum cz_k Hz_k = x^4 - x^2
    mult = [dict() for _ in K]
    for j, (f, offset) in enumerate([(f1, 3), (f2, 6)]):
        gj = [place(p, offset) for p in g]
        tau = {}
        for d, p in zip(TARGET, gj):
            tau = p_add(tau, p_mul(p_const(d, n), p))
        # f = f * sum g_k G_jk - tau * (f - f^2), and f - f^2 = q * (x^4 - x^2)
        rest = p_add(f, p_mul(f, f), -1)
        q = member_exact([place(quartic, 0)], rest, p_degree(rest))[0]
        for k in range(3):
            mult[3 + 3 * j + k] = p_add(mult[3 + 3 * j + k], p_mul(f, gj[k]))
            mult[k] = p_add(mult[k], p_mul(p_mul(tau, q), cz[k]), -1)
    # the refutation of the formula: 1 = (1 - X)^3 + X^3 - 3 (X^2 - X), at X = x^2
    for k in range(3):
        mult[k] = p_add(mult[k], p_mul(p_const(3, n), cz[k]), -1)
    one = p_const(1, n)
    up = p_add(combine(K, mult), one, -1) == {}
    degree_up = max(p_degree(p_mul(f, m)) for f, m in zip(K, mult) if m)
    # back: every block goes to a point; the variable block to the line through its two points
    X = ["X"]
    line = [parse("X", X), parse("-3/2*X", X), parse("-1/4 + 27/4*X", X)]
    point = [p_const(0, 1), p_const(0, 1), p_const(Fraction(-1, 4), 1)]
    images = line + point + point
    Ks = [substitute(f, images, 1) for f in K]
    ms = [substitute(m, images, 1) for m in mult]
    down = p_add(combine(Ks, ms), p_const(1, 1), -1) == {}
    boolean, a1, a2 = parse("X^2 - X", X), parse("(1 - X)^3", X), parse("X^3", X)
    in_ideal = all(member_exact([boolean, a1, a2], f, max(p_degree(f), 3)) is not None for f in Ks if f)
    degree_down = max(p_degree(p_mul(f, m)) for f, m in zip(Ks, ms) if m and f)
    ok = up and down and in_ideal and degree_up <= 2 * 3 + 18 and degree_down <= degree_up
    return [{"check": "refutation of the formula to refutation of its map", "formula_degree": 3,
             "map_degree": degree_up, "bound": 2 * 3 + 18, "exact": up},
            {"check": "and back by substitution", "degree": degree_down, "exact": down,
             "axioms_land_in_the_ideal_of_the_formula": in_ideal}], ok


def main():
    ok = True
    for part in (gadget_checks, curve_check, transfer_check):
        lines, good = part()
        ok &= good
        for line in lines:
            print(json.dumps(line))
    print(json.dumps({"ok": ok}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
