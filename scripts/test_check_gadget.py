#!/usr/bin/env python3
"""Tests of check_gadget.py: python3 scripts/test_check_gadget.py"""
import itertools
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import Refused, check, determinant, p_add, p_const, p_mul, parse  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
BASELINE = json.load(open(os.path.join(HERE, "..", "submissions", "alpoge-stambler", "gadget.json")))


def refused(gadget, word):
    try:
        check(gadget)
    except Refused as e:
        assert word in str(e), (word, str(e))
        return
    raise AssertionError("accepted: %r" % gadget)


def main():
    v = check(BASELINE)
    assert v == {"ok": True, "variables": 3, "degree": 7, "jacobian": "-2", "value": ["-1/4", "0", "0"]}, v
    # the third point of the fibre works as well
    assert check(dict(BASELINE, points=[["1", "-3/2", "13/2"], ["-1", "3/2", "13/2"]]))["ok"]
    # the parser: precedence, unary minus, both power signs, rationals
    assert parse("-x^2 + 2*x*y - (y - 1/2)**2", ["x", "y"]) == parse("-(x - y)^2 + y - 1/4", ["x", "y"])
    assert parse("y^2/12 - 21*x*y/2 + 3/2*x", ["x", "y"]) == parse("(y*y - 126*x*y + 18*x)/12", ["x", "y"])
    refused({"variables": ["x"], "map": ["x/0"], "points": [["0"], ["1"]]}, "division")
    refused({"variables": ["x"], "map": ["1/x"], "points": [["0"], ["1"]]}, "division")
    refused(dict(BASELINE, points=[["0", "0", "-1/4"], ["0", "0", "-1/4"]]), "same point")
    refused(dict(BASELINE, points=[["0", "0", "-1/4"], ["1", "1", "1"]]), "different values")
    # an invertible map has no two such points; a map with a varying Jacobian is not a gadget
    refused({"variables": ["x", "y"], "map": ["x + y^2", "y"], "points": [["0", "0"], ["1", "0"]]}, "different values")
    refused({"variables": ["x", "y"], "map": ["x^2", "y"], "points": [["1", "0"], ["-1", "0"]]}, "not a nonzero constant")
    refused({"variables": ["x", "y"], "map": ["x", "x"], "points": [["0", "0"], ["0", "1"]]}, "is zero")
    refused({"variables": ["x"], "map": ["__import__('os')"], "points": [["0"], ["1"]]}, "cannot read")
    refused({"variables": ["x"], "map": ["x^x"], "points": [["0"], ["1"]]}, "exponent")
    refused({"variables": ["x"], "map": ["x"], "points": [["0"], [1]]}, "coordinate")
    # the determinant against the sum over all permutations, on random sparse matrices
    random.seed(11)
    for _ in range(300):
        n = random.randint(1, 5)
        names = ["v%d" % i for i in range(n)]
        pool = ["0"] * random.randint(1, 6) + ["1", "v0", "v0*v0 - 2", "3 - v0", "v0^2 + 1/2", "v%d" % (n - 1), "v0*v%d + 1" % (n - 1)]
        mat = [[parse(random.choice(pool), names) for _ in range(n)] for _ in range(n)]
        want = {}
        for perm in itertools.permutations(range(n)):
            term = p_const(1, n)
            for i in range(n):
                term = p_mul(term, mat[i][perm[i]])
            inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
            want = p_add(want, term, -1 if inversions % 2 else 1)
        assert determinant(mat, n) == want
    print("ok")


if __name__ == "__main__":
    main()
