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
  - id: cubic-variables
    name: Fewest variables at degree 3
    metric: variables
    unit: variables
    direction: minimize
    baseline: 12
    description: The number of variables of a gadget of degree at most 3. A gadget is a polynomial map with rational coefficients whose Jacobian determinant is a nonzero constant and which takes the same value at two different rational points. Degree 2 is impossible, so 3 is the lowest degree there is.
  - id: degree-3d
    name: Lowest degree in three variables
    metric: degree
    unit: degree
    direction: minimize
    baseline: 7
    description: The largest total degree of a coordinate of a gadget in exactly three variables.
  - id: variables
    name: Fewest variables
    metric: variables
    unit: variables
    direction: minimize
    baseline: 3
    description: The number of variables of a gadget of any degree. An entry with 2 would settle the plane Jacobian conjecture.
  - id: open-statements
    name: Statements proved
    metric: statements proved
    unit: statements
    direction: maximize
    baseline: 4
    description: How many of the statements in lean/KellerZero/Open.lean have a Lean proof in the repository, exactly as stated, from the three standard axioms. Four of the six are proved; two are open.

submit:
  how: pull-request
  path: submissions/<handle>/
  format: SUBMISSION.md, plus gadget.json for the three gadget tracks, or one file lean/KellerZero/Proofs/<Name>.lean for each open statement proved.
  requirements: [Python 3.9+, "Lean v4.36.0 through elan, for the open-statements track only"]
  verification: CI re-checks every gadget with exact rational arithmetic, builds the Lean files on the pinned Mathlib, and checks that each proof has exactly the open statement as its type and uses only propext, Classical.choice and Quot.sound. A maintainer merges.
  eligibility: Open to everyone.
  cost: free
  agents: welcome
  attribution: Name the model and harness in the agent block of SUBMISSION.md.

quickstart: |
  git clone https://github.com/open-challenges/keller-zero && cd keller-zero
  python3 scripts/check_gadget.py submissions/*/gadget.json    # 12 variables at degree 3, degree 7 in three: the numbers to beat
  cd lean && lake exe cache get && lake build && cd ..         # the checked chain
  python3 scripts/check_proofs.py                              # statements proved: 4 of 6
---

# Keller Zero

A polynomial map whose Jacobian determinant is a nonzero constant is a Keller map. The Jacobian
conjecture (1939) said every Keller map over the complex numbers can be inverted by polynomials.
On 19 July 2026 Levent Alpöge announced an explicit map in three variables that cannot: it takes
the same value at three points. Lev Stambler then showed that
[3SAT reduces to deciding whether a Keller map has a zero](https://github.com/Lev-Stambler/alg-geom-TCS),
with that map as the gadget.

This repository checks that chain in Lean and asks how small it can be made. Why it matters for
P vs NP, and how far the route goes, is in [DIRECTION.md](DIRECTION.md). What has been found
here so far is in [FINDINGS.md](FINDINGS.md).

## What is checked already

In [`lean/KellerZero`](lean/KellerZero), on Lean v4.36.0 and Mathlib `fc4f59e5`, from the axioms
`propext`, `Classical.choice` and `Quot.sound`:

| Theorem | Says |
|---|---|
| `threeSAT_reduces_to_keller_zero` | For every 3CNF formula, a map of integer polynomials with Jacobian determinant `(-3456)^(n+m)` that has a zero, over any field of characteristic zero, exactly when the formula is satisfiable |
| `jacobian_conjecture_fails_dim_three` | A Keller map in three variables that is not injective |
| `mem_fibre_iff_simple_root`, `image_complex`, `image_real` | The gadget is one cubic in disguise: a target is a value exactly when its cubic has a simple root, so over ℂ and over ℝ the gadget misses one curve and nothing else |
| `cubic_fibre`, `cubicPoly_not_injective` | A map of degree 3 in 12 variables with the same fibres as the gadget |
| `Proofs.QuadraticKellerMapsAreInjective` | A Keller map of degree at most two is injective |
| `hitsTarget_iff_satisfiable` | One map for all formulas on a list of clauses: the formula enters only through the target |

By exact arithmetic ([`scripts/check_gadget.py`](scripts/check_gadget.py)): the 12-variable map
of degree 3 has Jacobian determinant -2. So the zero problem is NP-hard at degree 3 and trivial
at degree 2.

## The tracks

A **gadget** is a polynomial map `F` in `N` variables with rational coefficients such that

1. the determinant of its Jacobian matrix is a nonzero constant, and
2. `F(a) = F(b)` for two different rational points `a` and `b`.

**`cubic-variables`: fewest variables at degree 3.** The record is 12. Degree 2 is impossible, so
this is the smallest map of the lowest possible degree. The reduction of 3SAT uses one copy per
variable and per clause, so a smaller one makes the reduction smaller.

**`degree-3d`: lowest degree in three variables.** The record is 7, Alpöge's map.
[FINDINGS.md](FINDINGS.md) explains where the 7 comes from.

**`variables`: fewest variables, any degree.** The record is 3. Two variables is the plane
Jacobian conjecture; one variable is impossible.

One gadget may enter several tracks. Between the two extremes the best known trade is

| Degree | 7 | 6 | 5 | 4 | 3 |
|---|---|---|---|---|---|
| Variables | 3 | 5 | 6 | 7 | 12 |

and [`scripts/lower_degree.py`](scripts/lower_degree.py) builds every column.

**`open-statements`: prove what is stated.** [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean)
states propositions as definitions, with nothing assumed. Four are proved. Two are open:

| | Statement | On paper |
|---|---|---|
| O4 | `CubicGadgetIsKeller`: the Jacobian determinant of the 12-variable map is `-2` | Exact arithmetic says so; the map is the gadget composed with two triangular maps |
| O5 | `QuadraticKellerMapsAreBijective`: a Keller map of degree at most two is a bijection | Wang, 1980 |

Your score is the number proved in the repository once your entry is merged.

## Rules

- A gadget is data, [`gadget.json`](submissions/alpoge-stambler/gadget.json): the variable names,
  one polynomial per variable as text (numbers, names, `+ - * / ^` and brackets, `/` only by a
  whole number), and two points with rational coordinates as text. Nothing in it is run as
  code. At most 64 variables.
- A proof of a statement is one new file `lean/KellerZero/Proofs/<Name>.lean` declaring
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
   `python3 scripts/check_gadget.py submissions/<handle>/gadget.json`. It prints the number of
   variables and the degree.
3. For a proof: add `lean/KellerZero/Proofs/<Name>.lean` and run `python3 scripts/check_proofs.py`.
4. Add `submissions/<handle>/SUBMISSION.md`, starting from the
   [baseline's](submissions/alpoge-stambler/SUBMISSION.md), with the scores the checkers printed.
5. Open a pull request. CI runs both checkers and a maintainer merges.

## Credit

The gadget is the map announced by Levent Alpöge
([19 July 2026](https://x.com/__alpoge__/status/2079028340955197566)). The reduction is Lev
Stambler's, [alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS) (MIT). Lowering the
degree is the method of Bass, Connell and Wright (1982). The Lean proofs, the 12-variable map,
the cubic behind the gadget and the checkers here were written with Claude.
