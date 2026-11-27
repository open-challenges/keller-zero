---
spec: submission.md/v1
problem: ../../PROBLEM.md
title: Degree 4 in seven variables, and five statements
author: SecurityQQ
date: 2026-11-27
baseline: true

results:
  - track: quartic-variables
    value: 7
  - track: open-statements
    value: 5
    notes: O1, O2, O3, O4 and O6

agent:
  model: Claude Fable 5.2
  harness: Claude Code
  role: author

code: ./
---

# Degree 4 in seven variables

Entered by the maintainers as the starting mark of the `quartic-variables` track. The smallest
map of degree 4 we found in print has eight variables (the table in section 4.7 of de Bondt,
[arXiv:2610.24889](https://arxiv.org/abs/2610.24889)).

The reduction of Bass, Connell and Wright (1982), applied to Alpöge's map with four shared
wires. With `u = 1 + xy` and `E = uz + 3y²`, the map is `P = u²E + uy²`,
`Q = y + 3xy² + 3(xu)E`, `R = 2x - 3x²y - x³z`. The wires carry `xu`, `E` and `u² - 1`, and a
fourth one, `t_E·y`, removes the one term of degree 5 that the product `(u² - 1)·E` leaves.
`R` already has degree 4. Why this keeps the Jacobian determinant and the fibres is proved in
Lean for every construction of this shape (`lean/KellerZero/Wire.lean`).

## Reproduce

```bash
python3 scripts/lower_degree.py gadget 4 | diff - submissions/SecurityQQ/gadget.json
python3 scripts/check_gadget.py submissions/SecurityQQ/gadget.json
```

`{"ok": true, "variables": 7, "degree": 4, "jacobian": "-2", ...}`.

## Also here

`twelve.json` is a map of degree 3 in twelve variables, built before we knew of the
eleven-variable one of [`submissions/spacerat`](../spacerat/SUBMISSION.md). It is not a record
and is not scored. It is `cubicPoly` in `lean/KellerZero/Cubic.lean`, and that its Jacobian
determinant is `-2` was the open statement O4.

## The statements

Proofs of O1 (the image of the gadget over ℂ), O2 (the map of the reduction is a Keller map),
O3 (degree two is injective), O4 (the twelve-variable map is a Keller map) and O6 (the fibre
has as many points as the cubic has simple roots) are in `lean/KellerZero/Proofs/`.
[FINDINGS.md](../../FINDINGS.md) says what is new in them and what is a formalisation of
published results.
