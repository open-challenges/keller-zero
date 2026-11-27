# Keller Zero

**3SAT reduces to finding a zero of a polynomial map of degree 3 with constant Jacobian
determinant, and this is checked in Lean.** With the generalized Riemann hypothesis the problem
is NP-complete, and it is trivial at degree 2.

In July 2026 Levent Alpöge announced an explicit polynomial map in three variables whose
Jacobian determinant is constant and which is not injective, a counterexample to the Jacobian
conjecture. Lev Stambler [turned it into a reduction](https://github.com/Lev-Stambler/alg-geom-TCS):
a 3CNF formula becomes a polynomial map with constant Jacobian that has a zero exactly when the
formula is satisfiable. A question conjectured to have the same answer every time is NP-hard.
This repository checks that chain in Lean, lowers it to the least possible degree, and
classifies the questions one can ask about such maps.

Nobody has proved P = NP this way, and nothing here is a lower bound on computation.
[COMPLEXITY.md](COMPLEXITY.md) says what such a proof would have to do.

- [FINDINGS.md](FINDINGS.md): what has been found here, and what turned out to be known.
- [COMPLEXITY.md](COMPLEXITY.md): how hard the questions about these maps are.
- [PROBLEM.md](PROBLEM.md): the tracks, the rules, how to enter.
- [DIRECTION.md](DIRECTION.md): the research direction and where it ended.
- [AGENTS.md](AGENTS.md): the short version for coding agents.

## Found here

1. **The reduction at degree 3, in Lean.** For every 3CNF formula with `n` variables and `m`
   clauses: a map of `11n + 14m` integer polynomials of degree at most 3, with Jacobian
   determinant `(-3456)^(n+m)`, that has a zero exactly when the formula is satisfiable. A map
   of degree 2 with constant Jacobian determinant is injective, so 3 is where hardness starts.
2. **The complex zero problem is in NP**, assuming the generalized Riemann hypothesis: a zero
   modulo a prime lifts to a complex zero by Hensel's lemma. So the problem is NP-complete.
   Counting zeros is #P-hard. (Proofs on paper, from published theorems.)
3. **Recognising such a map is identity testing**: in coRP, and as hard as testing whether a
   determinant of linear forms is constant, already at degree 2.
4. **Refuting the map is as hard as refuting the formula**: a Nullstellensatz refutation of one
   gives one of the other, with the same degree one way and at most twice the degree plus 24
   the other way (Lean, both ways). The same on paper for polynomial calculus and sums of
   squares.
5. **Seven variables at degree 4**, one fewer than the published eight.

A first version of this page also listed the description of the gadget by a cubic. That was
published by others on 20 July 2026; what is here is its proof in Lean.
[FINDINGS.md](FINDINGS.md) has the corrections.

## Leaderboard

| Track | Record | Entry | Date |
|---|---|---|---|
| `cubic-variables`: fewest variables at degree 3 | 11 (baseline) | [The eleven-variable map of degree 3](submissions/spacerat/SUBMISSION.md), Spacerat | 2026-07-20 |
| `quartic-variables`: fewest variables at degree 4 | 7 (baseline) | [Degree 4 in seven variables](submissions/SecurityQQ/SUBMISSION.md) | 2026-11-27 |
| `degree-3d`: lowest degree in three variables | 7 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `variables`: fewest variables | 3 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `open-statements`: statements proved | 6 of 8 (baseline) | [O1, O2, O3, O4, O6, O8](submissions/SecurityQQ/SUBMISSION.md) | 2026-11-27 |

An entry with 2 variables would settle the plane Jacobian conjecture.

## Checked in Lean

Lean v4.36.0, Mathlib `fc4f59e5`, axioms `propext`, `Classical.choice`, `Quot.sound` only.
CI rebuilds everything on every push.

| Theorem ([`lean/KellerZero`](lean/KellerZero)) | Says |
|---|---|
| `threeSAT_reduces_to_cubic_keller_zero` | The reduction at degree 3: `11n + 14m` variables, determinant `(-3456)^(n+m)`, a zero exactly when the formula is satisfiable |
| `keller_zero_hard_exactly_from_degree_three` | Degree 2 is injective and degree 3 carries 3SAT, in one statement |
| `threeSAT_reduces_to_keller_zero` | Stambler's theorem, degree 7 |
| `pderiv_bind₁`, `det_wireExt`, `aeval_wireExt_eq_zero_iff` | The chain rule, and that adding wires changes neither the Jacobian determinant nor the zeros |
| `det_cubic11Map`, `totalDegree_cubic11Map`, `cubic11Map_not_injective` | The eleven-variable map of degree 3 |
| `refutation_of_formula`, `Proofs.RefutationOfMap` | A refutation of the map gives a refutation of the formula of no larger degree, and conversely with at most twice the degree plus 24 |
| `det_jacobian_bilinearMap` | The Jacobian determinant of `(x, y) ↦ (x, M(x)y)` is `det M(x)` |
| `curve_certificate`, `target_certificate`, `zeros_of_H` | Explicit certificates: the omitted curve and the three zeros of the gadget |
| `det_jacobian`, `jacobian_conjecture_fails_dim_three` | The gadget has Jacobian determinant -2 and is not injective |
| `mem_fibre_iff_simple_root`, `image_complex`, `image_real`, `Proofs.FibreCount` | The fibres of the gadget are the simple roots of a cubic; it misses one curve and nothing else |
| `hitsTarget_iff_satisfiable` | One map for all formulas: the formula enters only through the target |

Open in Lean, stated in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean): bijectivity at
degree two (O5), and that a zero modulo a prime gives a complex zero (O7).

## Try it

```bash
git clone https://github.com/open-challenges/keller-zero && cd keller-zero
python3 scripts/check_gadget.py submissions/*/gadget.json     # exact, no installs
python3 scripts/lower_degree.py formula "1 2 3, -1 -2 -3"     # the map of a formula at degree 3
python3 scripts/witness.py                                    # short proofs that a zero exists
python3 scripts/certificates.py && python3 scripts/recognition.py && python3 scripts/count_zeros.py
cd lean && lake exe cache get && lake build && cd ..          # Lean through elan
python3 scripts/check_proofs.py
```

## Credit and license

The gadget is Levent Alpöge's map
([announcement](https://x.com/__alpoge__/status/2079028340955197566)); the reduction is Lev
Stambler's ([alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS), MIT); the
eleven-variable map of degree 3 is
[Spacerat's](https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8); lowering the
degree is the method of Bass, Connell and Wright. Earlier machine-checked proofs that Alpöge's
map is a counterexample exist in Lean (Paul Lezeau) and in Isabelle (Archive of Formal Proofs,
`Jacobian_Counterexample`). The Lean proofs here, the reduction at degree 3, the notes and the
checkers were written with Claude. MIT license.

Listed on [Open Challenge List](https://openchallengelist.com).
