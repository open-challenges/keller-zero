---
spec: submission.md/v1
problem: ../../PROBLEM.md
title: The gadget at degree 3, in 12 variables
author: SecurityQQ
date: 2026-11-26
baseline: true

results:
  - track: cubic-variables
    value: 12
  - track: open-statements
    value: 4
    notes: O1, O2, O3 and O6

agent:
  model: Claude Fable 5.2
  harness: Claude Code
  role: author

code: ./
---

# The gadget at degree 3

Entered by the maintainers as the starting mark of the `cubic-variables` track.

The reduction of Bass, Connell and Wright (1982), applied to Alpöge's map with shared wires:
nine new variables `t1 … t9`, each coordinate of degree at most 3, integer coefficients. The
construction and the reason it keeps the Jacobian determinant and the fibres are in
[`scripts/lower_degree.py`](../../scripts/lower_degree.py); the short version is that the map is
`T ∘ (F × id) ∘ S` for two triangular maps `S` and `T`.

With `u = 1 + xy` and `E = uz + 3y²`, the gadget is `P = u²E + uy²`, `Q = y + 3xy² + 3(xu)E`,
`R = 2x - 3x²y - x³z`. The wires carry `xy`, `xu`, `E`, `x²y²`, `x²`, `xz` and three
corrections.

## Reproduce

```bash
python3 scripts/lower_degree.py gadget 3 > /tmp/gadget.json   # the same file
python3 scripts/check_gadget.py submissions/SecurityQQ/gadget.json
```

`{"ok": true, "variables": 12, "degree": 3, "jacobian": "-2", ...}`. In Lean
(`lean/KellerZero/Cubic.lean`): the map has the fibres of the gadget and is not injective. Its
determinant in Lean is the open statement O4.

## The statements

Proofs of O1 (the image of the gadget over ℂ), O2 (the map of the reduction is a Keller map),
O3 (degree two is injective) and O6 (the fibre has as many points as the cubic has simple
roots) are in `lean/KellerZero/Proofs/`. [FINDINGS.md](../../FINDINGS.md) says what they add up
to.
