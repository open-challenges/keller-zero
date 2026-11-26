#!/usr/bin/env python3
"""Tests of check_gadget.py: python3 scripts/test_check_gadget.py"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_gadget import Refused, check, parse  # noqa: E402

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
    refused(dict(BASELINE, points=[["0", "0", "-1/4"], ["0", "0", "-1/4"]]), "same point")
    refused(dict(BASELINE, points=[["0", "0", "-1/4"], ["1", "1", "1"]]), "different values")
    # an invertible map has no two such points; a map with a varying Jacobian is not a gadget
    refused({"variables": ["x", "y"], "map": ["x + y^2", "y"], "points": [["0", "0"], ["1", "0"]]}, "different values")
    refused({"variables": ["x", "y"], "map": ["x^2", "y"], "points": [["1", "0"], ["-1", "0"]]}, "not a nonzero constant")
    refused({"variables": ["x", "y"], "map": ["x", "x"], "points": [["0", "0"], ["0", "1"]]}, "is zero")
    refused({"variables": ["x"], "map": ["__import__('os')"], "points": [["0"], ["1"]]}, "cannot read")
    refused({"variables": ["x"], "map": ["x^x"], "points": [["0"], ["1"]]}, "exponent")
    refused({"variables": ["x"], "map": ["x"], "points": [["0"], [1]]}, "coordinate")
    print("ok")


if __name__ == "__main__":
    main()
