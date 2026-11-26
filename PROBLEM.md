---
spec: problem.md/v1
name: Keller Zero
tagline: 3SAT reduces to finding a zero of a polynomial map with constant Jacobian. Find smaller gadgets and machine-check the chain in Lean.
status: active
domain: formal-methods
tags: [p-vs-np, complexity-theory, np-hardness, jacobian-conjecture, algebraic-geometry, lean4, mathlib]
compute: cpu
compute_details: No GPU. A gadget is checked in under a second with Python's standard library. The Lean track needs Lean v4.36.0 and Mathlib's prebuilt cache, about 10 GB of disk; the repository's own files build in under a minute.
deadline: rolling
prizes: recognition only
organizer:
  name: Open Challenge List
  url: https://openchallengelist.com
website: https://github.com/open-challenges/keller-zero
leaderboard: https://github.com/open-challenges/keller-zero#leaderboard

tracks:
  - id: degree
    name: Lowest degree
    metric: degree
    unit: degree
    direction: minimize
    baseline: 7
    description: The largest total degree of a coordinate of a gadget, a polynomial map with rational coefficients whose Jacobian determinant is a nonzero constant and which takes the same value at two different rational points. Any number of variables up to 12. Degree 2 is impossible.
  - id: variables
    name: Fewest variables
    metric: variables
    unit: variables
    direction: minimize
    baseline: 3
    description: The number of variables of a gadget. An entry with 2 would settle the plane Jacobian conjecture.
  - id: open-statements
    name: Open statements proved
    metric: statements proved
    unit: statements
    direction: maximize
    baseline: 0
    description: How many of the statements in lean/KellerZero/Open.lean have a Lean proof in the repository, exactly as stated, from the three standard axioms. There are three today.

submit:
  how: pull-request
  path: submissions/<handle>/
  format: SUBMISSION.md, plus gadget.json for the degree and variables tracks, or one file lean/KellerZero/Proofs/<Name>.lean for each open statement proved.
  requirements: [Python 3.9+, "Lean v4.36.0 through elan, for the open-statements track only"]
  verification: CI re-checks every gadget with exact rational arithmetic, builds the Lean files on the pinned Mathlib, and checks that each proof has exactly the open statement as its type and uses only propext, Classical.choice and Quot.sound. A maintainer merges.
  eligibility: Open to everyone.
  cost: free
  agents: welcome
  attribution: Name the model and harness in the agent block of SUBMISSION.md.

quickstart: |
  git clone https://github.com/open-challenges/keller-zero && cd keller-zero
  python3 scripts/check_gadget.py submissions/alpoge-stambler/gadget.json   # degree 7, 3 variables: the numbers to beat
  cd lean && lake exe cache get && lake build && cd ..                      # the checked chain
  python3 scripts/check_proofs.py                                           # open statements proved: 0 of 3
---

# Keller Zero

A polynomial map whose Jacobian determinant is a nonzero constant is a Keller map. The Jacobian
conjecture (1939) said every Keller map over the complex numbers can be inverted by polynomials.
On 19 July 2026 Levent Alpöge announced an explicit map in three variables that cannot: it takes
the same value at three points. Lev Stambler then showed that
[3SAT reduces to deciding whether a Keller map has a zero](https://github.com/Lev-Stambler/alg-geom-TCS),
with that map as the gadget.

This repository checks that chain in Lean and asks how small it can be made. Why it matters for
P vs NP, and how far the route goes, is in [DIRECTION.md](DIRECTION.md).

## What is checked already

In [`lean/KellerZero`](lean/KellerZero), on Lean v4.36.0 and Mathlib `fc4f59e5`, from the axioms
`propext`, `Classical.choice` and `Quot.sound`:

| Theorem | Says |
|---|---|
| `det_jacobian` | The Jacobian determinant of the gadget is the constant -2, over any commutative ring |
| `jacobian_conjecture_fails_dim_three` | A Keller map in three variables that is not injective, over every field of characteristic zero |
| `fibre_zero` | The gadget takes the value (-1/4, 0, 0) at exactly three points |
| `omitted_curve` | The gadget never takes a value (t²/12, t, 4/(3t)) with t ≠ 0 |
| `exists_zero_reductionMap_iff_satisfiable` | The polynomial map built from a 3CNF formula has a zero exactly when the formula is satisfiable |
| `hitsTarget_iff_satisfiable` | One map for all formulas on a list of clauses: the formula enters only through the target |

## The tracks

**`degree` and `variables`: a smaller gadget.** A gadget is a polynomial map `F` in `N`
variables with rational coefficients such that

1. the determinant of its Jacobian matrix is a nonzero constant, and
2. `F(a) = F(b)` for two different rational points `a` and `b`.

The baseline has degree 7 and 3 variables. Your score on `degree` is the largest total degree of
a coordinate; on `variables` it is `N`. One gadget may enter both.

- Degree 2 is impossible: a Keller map of degree at most two is injective (Wang, 1980). Proving
  that in Lean is the open statement O3.
- The reduction of Bass, Connell and Wright (1982) trades degree for variables and ends at degree
  3. Nobody has entered the result of carrying it out. The checker takes up to 12 variables.
- Two variables is the plane Jacobian conjecture. One variable is impossible.

**`open-statements`: prove what is still open.** [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean)
states three propositions as definitions, with nothing assumed:

| | Statement | On paper |
|---|---|---|
| O1 | `ImageIsComplementOfCurve`: over the complex numbers the gadget misses the curve of `omitted_curve` and nothing else | A resultant computation, [`scripts/omitted_set.py`](scripts/omitted_set.py) |
| O2 | `ReductionMapIsKeller`: the Jacobian determinant of the map of the reduction is `(-3456)^(n+m)` | Block triangular |
| O3 | `QuadraticKellerMapsAreInjective`: a Keller map of degree at most two is injective | The derivative of a quadratic at the midpoint |

Your score is the number of them proved in the repository once your entry is merged.

## Rules

- A gadget is data, [`gadget.json`](submissions/alpoge-stambler/gadget.json): the variable names,
  one polynomial per variable as text (numbers, names, `+ - * ^` and brackets), and two points
  with rational coordinates as text. Nothing in it is run as code.
- A proof of an open statement is one new file `lean/KellerZero/Proofs/<Name>.lean` declaring
  `theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>`. It may import Mathlib and this
  repository's files. No `sorry`, no `native_decide`, no axioms beyond the three above.
- A pull request changes only `submissions/<handle>/` and, for a proof, its files under
  `lean/KellerZero/Proofs/`. A change to a statement, a checker or the baseline is not an entry;
  open an issue if a statement looks wrong.
- Ties go to the earlier entry. An entry that matches the record without beating it is listed
  below it.
- Give credit: say what your gadget or proof builds on.

## How to submit

1. Fork and clone. Run the quickstart.
2. For a gadget: write `submissions/<handle>/gadget.json` and run
   `python3 scripts/check_gadget.py submissions/<handle>/gadget.json`. It prints the two scores.
3. For a proof: add `lean/KellerZero/Proofs/<Name>.lean` and run `python3 scripts/check_proofs.py`.
4. Add `submissions/<handle>/SUBMISSION.md`, starting from the
   [baseline's](submissions/alpoge-stambler/SUBMISSION.md), with the scores the checkers printed.
5. Open a pull request. CI runs both checkers and a maintainer merges.

## Credit

The gadget is the map announced by Levent Alpöge
([19 July 2026](https://x.com/__alpoge__/status/2079028340955197566)). The reduction is Lev
Stambler's, [alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS) (MIT). The Lean proofs,
the omitted curve, the one-map form and the checkers here were written with Claude.
