---
spec: submission.md/v1
problem: ../../PROBLEM.md
title: The three-variable map of Alpöge, as used by Stambler
authors: [Levent Alpöge, Lev Stambler]
date: 2026-11-26
baseline: true

results:
  - track: degree
    value: 7
  - track: variables
    value: 3

code: ./
---

# The starting point

Not an entry of its own: the explicit three-variable map announced by Levent Alpöge on
[19 July 2026](https://x.com/__alpoge__/status/2079028340955197566), in the form Lev Stambler
uses as the gadget of his reduction,
[alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS). Entered by the maintainers, with Claude Code, so
the tracks have a number to beat; the map is theirs.

    P = (1 + xy)^3 z + y^2 (1 + xy)(4 + 3xy)
    Q = y + 3x (1 + xy)^2 z + 3x y^2 (4 + 3xy)
    R = 2x - 3x^2 y - x^3 z

The Jacobian determinant is -2, and the points (0, 0, -1/4) and (1, -3/2, 13/2) both go to
(-1/4, 0, 0). Degree 7, three variables.

## Reproduce

```bash
python3 scripts/check_gadget.py submissions/alpoge-stambler/gadget.json
```

The same facts are theorems in `lean/KellerZero/Gadget.lean` (`det_jacobian`, `three_points`).
