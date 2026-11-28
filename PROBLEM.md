---
spec: problem.md/v1
name: Keller Zero
tagline: 3SAT reduces to finding a zero of a polynomial map of degree 3 with constant Jacobian, checked in Lean. Find smaller gadgets and prove the statements still open.
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
    baseline: 11
    description: The number of variables of a gadget of degree at most 3. A gadget is a polynomial map with rational coefficients whose Jacobian determinant is a nonzero constant and which takes the same value at two different rational points. Degree 2 is impossible, so 3 is the lowest degree there is. The mark of 11 was published by Spacerat on 20 July 2026; the record is 10.
  - id: quartic-variables
    name: Fewest variables at degree 4
    metric: variables
    unit: variables
    direction: minimize
    baseline: 8
    description: The number of variables of a gadget of degree at most 4. The mark of 8 is from a table in de Bondt, arXiv:2610.24889; the record is 7. In three variables degree at most 4 is impossible if a 2026 preprint of Wang and Yan is right.
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
    baseline: 0
    description: How many of the statements in lean/KellerZero/Open.lean have a Lean proof in the repository, exactly as stated, from the three standard axioms. Six of the eight are proved; two are open.

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
  python3 scripts/check_gadget.py submissions/*/gadget.json    # 10 variables at degree 3, 7 at degree 4, degree 7 in three: the numbers to beat
  cd lean && lake exe cache get && lake build && cd ..         # the checked chain
  python3 scripts/check_proofs.py                              # statements proved: 6 of 8
---

# Keller Zero

A polynomial map whose Jacobian determinant is a nonzero constant is a Keller map. The Jacobian
conjecture (1939) said every Keller map over the complex numbers can be inverted by polynomials.
On 19 July 2026 Levent Alpöge announced an explicit map in three variables that cannot: it takes
the same value at three points. Lev Stambler then showed that
[3SAT reduces to deciding whether a Keller map has a zero](https://github.com/Lev-Stambler/alg-geom-TCS),
with that map as the gadget.

This repository checks that chain in Lean, brings it down to degree 3, the least possible, and
works out how hard the questions about such maps are. What has been found is in
[FINDINGS.md](FINDINGS.md) and [COMPLEXITY.md](COMPLEXITY.md). Why it was started, and why as a
road to a lower bound it has reached its end, is in [DIRECTION.md](DIRECTION.md).

## What is checked already

In [`lean/KellerZero`](lean/KellerZero), on Lean v4.36.0 and Mathlib `fc4f59e5`, from the axioms
`propext`, `Classical.choice` and `Quot.sound`:

| Theorem | Says |
|---|---|
| `threeSAT_reduces_with_one_checker` | For every 3CNF formula, a map of `10n + ⌈m/2⌉ + 12` integer polynomials of degree at most 3 with constant nonzero Jacobian determinant that has a zero, over any field of characteristic zero, exactly when the formula is satisfiable |
| `threeSAT_reduces_to_cubic_keller_zero` | The same for Stambler's map lowered to degree 3: `10n + 13m` variables, Jacobian determinant `(-3456)^(n+m)` |
| `threeSAT_reduces_to_keller_zero` | The same for Stambler's map: degree 7, `3n + 3m` variables |
| `Proofs.QuadraticKellerMapsAreInjective` | A Keller map of degree at most two is injective, so degree 3 is where hardness starts |
| `det_wireExt`, `aeval_wireExt_eq_zero_iff` | Lowering the degree by adding wires never changes the Jacobian determinant or the zeros |
| `det_cubic10Map`, `cubic10Map_not_injective` | A map of degree 3 in ten variables is a Keller map and is not injective (and the same for the published eleven-variable one, `Cubic11.lean`) |
| `refutation_of_formula`, `Proofs.RefutationOfMap` | A Nullstellensatz refutation of "the map has no zero" gives one of the formula of no larger degree, and conversely with at most twice the degree plus 24 |
| `det_jacobian_bilinearMap` | The map `(x, y) ↦ (x, M(x)y)` has Jacobian determinant `det M(x)`: recognising Keller maps contains identity testing |
| `mem_fibre_iff_simple_root`, `image_complex`, `image_real`, `curve_certificate` | The gadget is one cubic in disguise and misses exactly one curve, over ℂ and over ℝ |

## The tracks

A **gadget** is a polynomial map `F` in `N` variables with rational coefficients such that

1. the determinant of its Jacobian matrix is a nonzero constant, and
2. `F(a) = F(b)` for two different rational points `a` and `b`.

**`cubic-variables`: fewest variables at degree 3.** The record is 10 (this repository,
27 November 2026); before it, 11, published by Spacerat on 20 July 2026. Degree 2 is
impossible, so this is the smallest map of the lowest possible degree. The reduction of 3SAT uses one copy per variable and per clause, so a smaller one makes
the reduction smaller.

**`quartic-variables`: fewest variables at degree 4.** The record is 7; the smallest published
before it has 8.

**`degree-3d`: lowest degree in three variables.** The record is 7, Alpöge's map. A preprint of
Wang and Yan ([arXiv:2610.36495](https://arxiv.org/abs/2610.36495)) proves that 4 or less is
impossible, and the repository
[royvanrijn/jacobian-research](https://github.com/royvanrijn/jacobian-research) lists a proof
that 5 is impossible too. If both are right, the only value left to try is 6. Neither was
checked here.

**`variables`: fewest variables, any degree.** The record is 3. Two variables is the plane
Jacobian conjecture; one variable is impossible.

One gadget may enter several tracks. The best known trade between the two is

| Degree | 7 | 6 | 5 | 4 | 3 |
|---|---|---|---|---|---|
| Variables | 3 | 4 | 5 | 7 | 10 |
| Due to | Alpöge | de Bondt | de Bondt | this repository | this repository |

The entries of de Bondt are cited from [arXiv:2610.24889](https://arxiv.org/abs/2610.24889) and
are not rebuilt in this repository.

**`open-statements`: prove what is stated.** [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean)
states propositions as definitions, with nothing assumed. Six are proved. Two are open:

| | Statement | On paper |
|---|---|---|
| O5 | `QuadraticKellerMapsAreBijective`: a Keller map of degree at most two is a bijection | Wang, 1980 |
| O7 | `WitnessIsSound`: a zero modulo a prime at which the Jacobian determinant is not zero gives a complex zero | Hensel's lemma and the Nullstellensatz; COMPLEXITY.md, Theorem 2 |

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
- Give credit: say what your gadget or proof builds on. If your gadget is already published,
  say where and by whom; the board is for the truth of the record, not for who typed it in.

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
Stambler's, [alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS) (MIT). The
first map of degree 3 with as few as eleven variables is Spacerat's
([20 July 2026](https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8)); the
ten-variable one is built the same way. Lowering
the degree is the method of Bass, Connell and Wright (1982). The description of the gadget by
a cubic was published on 20 July 2026 and after (see [FINDINGS.md](FINDINGS.md) for the
sources). The Lean proofs, the reduction at degree 3, the results of COMPLEXITY.md and the
checkers here were written with Claude.
