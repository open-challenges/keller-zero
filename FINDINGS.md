# Findings

27 November 2026, second version. The first version (26 November) was written without a
literature search and claimed too much; the corrections come first.

Labels: **Lean** (proved in [`lean/`](lean), three standard axioms), **Computed** (exact
arithmetic, script named), **Paper** (argued in this repository, not formalised), **Known**
(published by others; cited).

None of this is a lower bound on computation. It says what the object is, where its hardness
starts, and how hard it is.

## Corrections to the first version

| The first version said | What is true |
|---|---|
| "The gadget is one cubic in disguise" was found here | It was published on 20 July 2026, the day after the announcement: an [unsigned manuscript](https://www.ulam.ai/research/jacobian.pdf) proves that the preimages are the simple roots of a cubic, that the image is the complement of one curve, and that the map fails to be proper exactly on the discriminant surface. Gao ([arXiv:2608.00222](https://arxiv.org/abs/2608.00222), appendix) has the cubic in the very coordinates used here. Shaska ([arXiv:2607.20210](https://arxiv.org/abs/2607.20210)) has the grading, the monodromy group S₃ and the thin image over ℚ. What this repository adds is the proof in Lean and one explicit certificate (§3). |
| The 12-variable map of degree 3 was new | A map of degree 3 in **11** variables was [published on 20 July 2026](https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8) (author's handle Spacerat, generated with ChatGPT). Twelve-variable ones are due to van Rijn and to de Bondt ([arXiv:2610.24889](https://arxiv.org/abs/2610.24889)). Ours came later and is not a record. |
| The table of variables against degree was the best known | At degrees 6 and 5 de Bondt has 4 and 5 variables; we had 5 and 6. At degree 4 our 7 variables is one fewer than his 8 (§4). |

## 1. 3SAT reduces to the zero problem at degree 3, and this is checked in Lean

**Theorem (Lean: `threeSAT_reduces_to_cubic_keller_zero`).** For every 3CNF formula with `n`
variables and `m` clauses, `cubicReduction φ` is a map of `11n + 14m` integer polynomials in as
many variables, each of degree at most 3, whose Jacobian determinant is `(-3456)^(n+m)`, and
which has a zero over any field of characteristic zero exactly when the formula is satisfiable.

Stambler's map has degree 7. A map of degree 2 with constant nonzero Jacobian determinant is
injective (Lean) and bijective (Known: Wang, 1980), so 3 is the least degree at which the
question can be hard. `keller_zero_hard_exactly_from_degree_three` states both halves.

| Piece | Label |
|---|---|
| A *wire extension* of any map has the same Jacobian determinant and the same zeros (`det_wireExt`, `aeval_wireExt_eq_zero_iff`); the chain rule for substitution (`pderiv_bind₁`) | Lean |
| The eleven-variable map of degree 3 of 20 July 2026 is a wire extension of the gadget: determinant `-2`, degree 3, not injective (`det_cubic11Map`, `totalDegree_cubic11Map`, `cubic11Map_not_injective`) | Lean; the map is Known |
| Three more wires per clause carry the product of three literal values at degree 3 (`bind₁_prodS`, `totalDegree_remainder`) | Lean |
| The same map built independently and its determinant expanded exactly, for two formulas | Computed: `scripts/test_lower_degree.py` |

That a counterexample of degree 3 exists in some dimension follows from Bass, Connell and
Wright (1982), and explicit ones were published in July 2026. What we did not find anywhere is
the reduction at degree 3, or any machine-checked proof of it.

## 2. How hard the questions about these maps are

[COMPLEXITY.md](COMPLEXITY.md) has the statements and proofs. In one table:

| Result | Label |
|---|---|
| "Does a Keller map have a complex zero?" is in NP, assuming the generalized Riemann hypothesis: a zero modulo a prime that does not divide the Jacobian determinant lifts by Hensel's lemma. With §1 the problem is NP-complete | Paper, from Known results; witnesses checked by `scripts/witness.py` |
| Counting the zeros is #P-hard | Paper, from Lean facts; Computed on small formulas |
| Recognising a Keller map is in coRP and is as hard as identity testing for determinants of linear forms, already at degree 2 (`det_jacobian_bilinearMap`) | Lean for the key identity; Paper and Known for the rest |
| A Nullstellensatz refutation of "the map has no zero" gives one of the formula of no larger degree (`refutation_of_formula`), and conversely with degree at most twice plus 18. So some maps of degree 3 in `N` variables need certificates of degree `Ω(N)` | Lean; Paper; the lower bounds for formulas are Known |
| "Is this Keller map not injective?" is in NP under the same hypothesis | Paper |

Nobody has proved P = NP with these maps; COMPLEXITY.md §1 says what we found when we looked.

## 3. The gadget, in Lean

The description of the gadget by a cubic is Known (see the corrections). Checked here:

| Statement | Lean name |
|---|---|
| With `u = 1 + xy`, `w = 5 - 3u - x²z` and `m = uw`: `R = xw`, `xQ = 4u + 2 - 3u²w`, `x²P = u² + u - u³w`, and `m³ - 2m² + (QR)m - 2PR² = 0` | `R_eq_mul`, `mul_Q_eq`, `sq_mul_P_eq`, `cubic_eq_zero` |
| For `c ≠ 0`, `(a, b, c)` is a value exactly when `m³ - 2m² + bc·m - 2ac²` has a simple root; over ℂ the fibre has as many points as there are simple roots | `mem_fibre_iff_simple_root`, `Proofs.FibreCount` |
| Over ℂ and over ℝ the gadget takes every value off the curve `(t²/12, t, 4/(3t))` and none on it | `image_complex`, `image_real` |
| One identity, uniform in `t`, puts `4t` in the ideal of the equations of a point of the curve; so the curve is omitted over every field in which `2 ≠ 0` | `curve_certificate`, `not_on_curve` |
| The ideal of `H = 12F + (3, 0, 0)` contains `x³ - x`, `2y + 3x` and `4z + 1 - 27x²`, with explicit multipliers of degree at most 10: it is the ideal of the three zeros, over every field in which 2 and 3 are not zero | `cube_certificate`, `y_certificate`, `z_certificate`, `zeros_of_H` |

The real image is stated in none of the sources we read, though it follows at once from their
formulas. The certificates were found by exact linear algebra (`scripts/certificates.py`); we
do not know whether they are in print.

## 4. Variables against degree

The fewest variables known for a map with constant Jacobian determinant that is not injective,
by degree:

| Degree | 7 | 6 | 5 | 4 | 3 | 2 |
|---|---|---|---|---|---|---|
| Variables | 3 | 4 | 5 | **7** | 11 | impossible |
| Due to | Alpöge | de Bondt | de Bondt | this repository | Spacerat | Wang, 1980 |

Ours is the entry at degree 4: `python3 scripts/lower_degree.py gadget 4` prints it and
`scripts/check_gadget.py` checks it (Computed). The table in de Bondt's paper has 8 there. The
entries of de Bondt are cited from his paper, not rebuilt here. In three variables, degree 7 is
the least known; a preprint (Wang and Yan, [arXiv:2610.36495](https://arxiv.org/abs/2610.36495))
proves that degree at most 4 is impossible there.

## 5. Stambler's theorem, machine-checked

`threeSAT_reduces_to_keller_zero` (Lean): for every 3CNF formula, `reductionMap φ` is a map of
`3n + 3m` integer polynomials of degree 7 whose Jacobian determinant is `(-3456)^(n+m)` and
which has a zero, over every field of characteristic zero, exactly when the formula is
satisfiable. `hitsTarget_iff_satisfiable` is the version with one map for all formulas on a
list of clauses.

## What is still open here

- O5 in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean): bijectivity at degree 2, in
  Lean. The other five statements are proved.
- Fewer than 11 variables at degree 3; fewer than 7 at degree 4.
- The questions at the end of COMPLEXITY.md: the hypothesis in the NP bound, hardness of
  "not injective", the real and rational zero problems.
- Everything in section 4 of [DIRECTION.md](DIRECTION.md): no lower bound on computation is in
  sight along this road.

## What was not checked

- The literature search was by keyword (arXiv, GitHub, Zenodo, X, MathOverflow) on
  27 November 2026. Results that are short may be folklore, or in a paper we did not find.
- The papers cited as Known were read for the statements quoted; their proofs were not
  re-checked. Several are preprints.
