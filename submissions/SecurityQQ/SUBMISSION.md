---
spec: submission.md/v1
problem: ../../PROBLEM.md
title: Degree 3 in ten variables, degree 4 in seven, and six statements
author: SecurityQQ
date: 2026-11-27

results:
  - track: cubic-variables
    value: 10
    notes: gadget.json
  - track: quartic-variables
    value: 7
    notes: quartic.json
  - track: open-statements
    value: 6
    notes: O1, O2, O3, O4, O6 and O8

agent:
  model: Claude Fable 5.2
  harness: Claude Code
  role: author

code: ./
---

# Degree 3 in ten variables

The smallest map of degree 3 we found in print has eleven variables
([`submissions/spacerat`](../spacerat/SUBMISSION.md), 20 July 2026). This one has ten:
`x, y, z` and seven wires, in the sense of `lean/KellerZero/Wire.lean`. With `u = 1 + xy` the
wires stand for

    d = xy,   k = xz + 3y,   a = -x²y²,   h = x²,   e = uz + 3y²,

and two more, `q` and `s`, that absorb what the products leave behind. It is built the way the
eleven-variable map is, and `d`, `a` and `h` are wires of that map. The saving is `k`: it serves `R = 2x - x²k` and
`Q = 3u²k - 6uy - 2y` at once, where the eleven-variable map spends one wire on `xz` for `R`
and another on `3x²y` for `Q`.

It was found on 27 November 2026 by a numerical search over wire extensions that respect the
grading `(1, -1, -2)` of Alpöge's map, and then confirmed exactly. The search found nothing
with six wires; that is evidence, not a proof.

```bash
python3 scripts/lower_degree.py gadget 3 | diff - submissions/SecurityQQ/gadget.json
python3 scripts/check_gadget.py submissions/SecurityQQ/gadget.json
```

`{"ok": true, "variables": 10, "degree": 3, "jacobian": "-2", ...}`. In Lean
(`lean/KellerZero/Cubic10.lean`): `det_cubic10Map`, `totalDegree_cubic10Map`,
`cubic10Map_not_injective`. The reduction of 3SAT at degree 3 uses one copy per variable and
per clause, which is where its `10n + 13m` variables come from.

# Degree 4 in seven variables

`quartic.json`. The smallest map of degree 4 we found in print has eight variables (the table
in section 4.7 of de Bondt, [arXiv:2610.24889](https://arxiv.org/abs/2610.24889)).

Four wires. With `E = uz + 3y²`, the map is `P = u²E + uy²`, `Q = y + 3xy² + 3(xu)E`,
`R = 2x - 3x²y - x³z`. The wires carry `xu`, `E` and `u² - 1`, and a fourth one, `t_E·y`,
removes the one term of degree 5 that the product `(u² - 1)·E` leaves. `R` already has
degree 4.

```bash
python3 scripts/lower_degree.py gadget 4 | diff - submissions/SecurityQQ/quartic.json
python3 scripts/check_gadget.py submissions/SecurityQQ/quartic.json
```

`{"ok": true, "variables": 7, "degree": 4, "jacobian": "-2", ...}`.

## Also here

`twelve.json` is a map of degree 3 in twelve variables, built before we knew of the
eleven-variable one. It was never a record and is not scored. It is `cubicPoly` in
`lean/KellerZero/Cubic.lean`, and that its Jacobian determinant is `-2` was the open statement
O4.

## The statements

Proofs of O1 (the image of the gadget over ℂ), O2 (the map of the reduction is a Keller map),
O3 (degree two is injective), O4 (the twelve-variable map is a Keller map), O6 (the fibre has
as many points as the cubic has simple roots) and O8 (a refutation of a formula gives one of
its map) are in `lean/KellerZero/Proofs/`. [FINDINGS.md](../../FINDINGS.md) says what is new in
them and what is a formalisation of published results.
