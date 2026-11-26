#!/usr/bin/env python3
"""Check a gadget: a polynomial map with rational coefficients whose Jacobian determinant is a
nonzero constant and which takes the same value at two different rational points.

    python3 scripts/check_gadget.py submissions/<handle>/gadget.json [more.json ...]

Everything is exact rational arithmetic from the standard library. The file is data: polynomials
are read by the small parser below (numbers, variable names, + - * ^ and parentheses), never
evaluated as code. Prints one JSON verdict per file; exit code 0 when every file passes.

The scores: `degree` is the largest total degree of a coordinate, `variables` is the number of
variables.
"""
import json
import re
import sys
from fractions import Fraction
from itertools import combinations

MAX_VARIABLES = 12         # the determinant is expanded exactly, over column sets
MAX_TERMS = 200_000        # of any polynomial met on the way
MAX_BYTES = 1_000_000      # of a gadget file
TOKEN = re.compile(r"\s*(?:(\d+(?:/\d+)?)|([A-Za-z_][A-Za-z_0-9]*)|(\*\*|[-+*^()]))")


class Refused(Exception):
    pass


def p_const(c, n):
    return {(0,) * n: Fraction(c)} if c else {}


def p_add(a, b, sign=1):
    out = dict(a)
    for e, c in b.items():
        v = out.get(e, 0) + sign * c
        if v:
            out[e] = v
        else:
            out.pop(e, None)
    return out


def p_mul(a, b):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(i + j for i, j in zip(ea, eb))
            v = out.get(e, 0) + ca * cb
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    if len(out) > MAX_TERMS:
        raise Refused("a polynomial grew past %d terms" % MAX_TERMS)
    return out


def p_pow(a, k, n):
    out = p_const(1, n)
    for _ in range(k):
        out = p_mul(out, a)
    return out


def p_diff(a, i):
    out = {}
    for e, c in a.items():
        if e[i]:
            out[e[:i] + (e[i] - 1,) + e[i + 1:]] = c * e[i]
    return out


def p_eval(a, point):
    total = Fraction(0)
    for e, c in a.items():
        term = c
        for x, k in zip(point, e):
            term *= x ** k
        total += term
    return total


def p_degree(a):
    return max((sum(e) for e in a), default=0)


def parse(text, names):
    """A polynomial from text. Grammar: sum of products of powers; ^ or ** takes a plain
    non-negative whole number; a number is digits or digits/digits."""
    n = len(names)
    tokens, at = [], 0
    while at < len(text):
        if text[at:].strip() == "":
            break
        m = TOKEN.match(text, at)
        if not m:
            raise Refused("cannot read the polynomial at: %r" % text[at:at + 20])
        tokens.append(m.group(1) or m.group(2) or m.group(3))
        at = m.end()
    pos = [0]

    def peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else None

    def take():
        pos[0] += 1
        return tokens[pos[0] - 1]

    def atom():
        t = peek()
        if t is None:
            raise Refused("the polynomial ends too early")
        take()
        if t == "(":
            v = total()
            if peek() != ")":
                raise Refused("a bracket is not closed")
            take()
            return v
        if t == "-":
            return p_add({}, power(), -1)
        if t == "+":
            return power()
        if t[0].isdigit():
            return p_const(Fraction(t), n)
        if t in names:
            i = names.index(t)
            return {(0,) * i + (1,) + (0,) * (n - i - 1): Fraction(1)}
        raise Refused("unknown name in a polynomial: %r" % t)

    def power():
        base = atom()
        if peek() in ("^", "**"):
            take()
            k = peek()
            if k is None or not k.isdigit() or int(k) > 64:
                raise Refused("an exponent must be a whole number from 0 to 64")
            take()
            return p_pow(base, int(k), n)
        return base

    def product():
        v = power()
        while peek() == "*":
            take()
            v = p_mul(v, power())
        return v

    def total():
        v = product()
        while peek() in ("+", "-"):
            sign = 1 if take() == "+" else -1
            v = p_add(v, product(), sign)
        return v

    v = total()
    if peek() is not None:
        raise Refused("cannot read the polynomial at: %r" % peek())
    return v


def determinant(rows, n):
    """Exact determinant of an n by n matrix of polynomials, by expansion over column sets."""
    best = {frozenset(): p_const(1, n)}
    for r in range(n - 1, -1, -1):
        nxt = {}
        for cols in combinations(range(n), n - r):
            total = {}
            for k, c in enumerate(cols):
                entry = rows[r][c]
                if not entry:
                    continue
                rest = frozenset(cols) - {c}
                total = p_add(total, p_mul(entry, best[rest]), 1 if k % 2 == 0 else -1)
            nxt[frozenset(cols)] = total
        best = nxt
    return best[frozenset(range(n))]


def show(q):
    return str(q.numerator) if q.denominator == 1 else "%d/%d" % (q.numerator, q.denominator)


def number(text):
    if not isinstance(text, str) or not re.fullmatch(r"-?\d+(/[1-9]\d*)?", text):
        raise Refused("a coordinate of a point must be text like \"-3/2\"")
    return Fraction(text)


def check(gadget):
    names = gadget.get("variables")
    if (not isinstance(names, list) or not 1 <= len(names) <= MAX_VARIABLES
            or not all(isinstance(v, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", v) for v in names)
            or len(set(names)) != len(names)):
        raise Refused("variables: 1 to %d different names" % MAX_VARIABLES)
    n = len(names)
    texts = gadget.get("map")
    if not isinstance(texts, list) or len(texts) != n or not all(isinstance(t, str) for t in texts):
        raise Refused("map: one polynomial, as text, for each of the %d variables" % n)
    polys = [parse(t, names) for t in texts]
    points = gadget.get("points")
    if not isinstance(points, list) or len(points) != 2 or not all(isinstance(p, list) and len(p) == n for p in points):
        raise Refused("points: two points with %d coordinates each" % n)
    a, b = ([number(c) for c in p] for p in points)
    if a == b:
        raise Refused("the two points are the same point")
    jac = determinant([[p_diff(f, j) for j in range(n)] for f in polys], n)
    if set(jac) != {(0,) * n}:
        raise Refused("the Jacobian determinant is not a nonzero constant" if jac else "the Jacobian determinant is zero")
    va, vb = [p_eval(f, a) for f in polys], [p_eval(f, b) for f in polys]
    if va != vb:
        raise Refused("the map takes different values at the two points")
    return {"ok": True, "variables": n, "degree": max(p_degree(f) for f in polys),
            "jacobian": show(jac[(0,) * n]), "value": [show(v) for v in va]}


def main(paths):
    if not paths:
        print(__doc__)
        return 2
    bad = 0
    for path in paths:
        try:
            with open(path, "rb") as f:
                raw = f.read(MAX_BYTES + 1)
            if len(raw) > MAX_BYTES:
                raise Refused("the file is larger than %d bytes" % MAX_BYTES)
            data = json.loads(raw.decode("utf-8"))
            if not isinstance(data, dict):
                raise Refused("the file must hold one JSON object")
            verdict = check(data)
        except Refused as e:
            verdict = {"ok": False, "why": str(e)}
        except (OSError, ValueError) as e:
            verdict = {"ok": False, "why": "cannot read the file: %s" % e}
        verdict["file"] = path
        bad += not verdict["ok"]
        print(json.dumps(verdict))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
