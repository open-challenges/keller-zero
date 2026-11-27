---
spec: submission.md/v1
problem: ../../PROBLEM.md
title: The eleven-variable map of degree 3
authors: [Spacerat]
date: 2026-07-20
baseline: true

results:
  - track: cubic-variables
    value: 11

code: ./
---

# The starting point at degree 3

Not an entry of its own. The map was published on 20 July 2026, one day after Alpöge's
announcement, as the gist
[11 variable cubic jacobian conjecture counterexample](https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8)
by the GitHub user Spacerat, who credits ChatGPT with the construction and a suggestion on
Reddit by u/zongshu to apply the reduction of Bass, Connell and Wright. It is also printed in
section 6 of [arXiv:2608.05392](https://arxiv.org/abs/2608.05392). Entered by the maintainers,
with Claude Code, so that the `cubic-variables` track starts from the true record; the map is
theirs. `gadget.json` has the variables and the polynomials as the gist gives them.

Eight new variables `a, b, c, d, q, s, h, k`, every coordinate of degree at most 3, integer
coefficients, 52 terms.

## Reproduce

```bash
python3 scripts/check_gadget.py submissions/spacerat/gadget.json
```

`{"ok": true, "variables": 11, "degree": 3, "jacobian": "-2", ...}`.

In Lean (`lean/KellerZero/Cubic11.lean`): the map is a wire extension of Alpöge's map, so its
Jacobian determinant is `-2` (`det_cubic11Map`), every coordinate has degree at most 3
(`totalDegree_cubic11Map`) and it is not injective (`cubic11Map_not_injective`). The reduction
of 3SAT at degree 3 (`lean/KellerZero/CubicReduction.lean`) uses one copy of it per variable
and per clause.
