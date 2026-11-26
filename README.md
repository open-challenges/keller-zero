# Keller Zero

**3SAT reduces to finding a zero of a polynomial map with constant Jacobian.** This repository
checks that chain in Lean, and asks how small the gadget behind it can be.

In July 2026 Levent Alpöge announced an explicit polynomial map in three variables whose
Jacobian determinant is constant and which is not injective, a counterexample to the Jacobian
conjecture. Lev Stambler [turned it into a reduction](https://github.com/Lev-Stambler/alg-geom-TCS):
a 3CNF formula becomes a polynomial map with constant Jacobian that has a zero exactly when the
formula is satisfiable. A question conjectured to have the same answer every time is NP-hard.

- [PROBLEM.md](PROBLEM.md): the tracks, the rules, how to enter.
- [FINDINGS.md](FINDINGS.md): what has been found here.
- [DIRECTION.md](DIRECTION.md): the research direction, and how far it goes toward P vs NP.
- [AGENTS.md](AGENTS.md): the short version for coding agents.

## Found here

1. **The gadget is one cubic in disguise.** A target `(a, b, c)` with `c ≠ 0` is a value of
   Alpöge's map exactly when `m³ - 2m² + bc·m - 2ac²` has a simple root, and the fibre has as
   many points as that cubic has simple roots. So over ℂ and over ℝ the map misses exactly one
   curve, where the cubic is a perfect cube. Proved in Lean.
2. **NP-hardness starts at degree 3, the lowest possible.** An explicit map of degree 3 in 12
   variables with Jacobian determinant -2 and the fibres of the gadget (exact arithmetic; the
   fibres in Lean) makes the reduction work at degree 3, in `12n + 15m` variables. At degree 2
   every such map is injective (Lean), so the problem is trivial there.
3. **Stambler's theorem is machine-checked end to end**, as one Lean statement.

## Leaderboard

| Track | Record | Entry | Date |
|---|---|---|---|
| `cubic-variables`: fewest variables at degree 3 | 12 (baseline) | [The gadget at degree 3](submissions/SecurityQQ/SUBMISSION.md) | 2026-11-26 |
| `degree-3d`: lowest degree in three variables | 7 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `variables`: fewest variables | 3 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `open-statements`: statements proved | 4 of 6 (baseline) | [O1, O2, O3, O6](submissions/SecurityQQ/SUBMISSION.md) | 2026-11-26 |

An entry with 2 variables would settle the plane Jacobian conjecture.

## Checked in Lean

Lean v4.36.0, Mathlib `fc4f59e5`, axioms `propext`, `Classical.choice`, `Quot.sound` only.
CI rebuilds everything on every push.

| Theorem ([`lean/KellerZero`](lean/KellerZero)) | Says |
|---|---|
| `threeSAT_reduces_to_keller_zero` | The map built from a formula has Jacobian determinant `(-3456)^(n+m)` and a zero exactly when the formula is satisfiable |
| `det_jacobian`, `jacobian_conjecture_fails_dim_three` | The gadget has Jacobian determinant -2 and is not injective |
| `mem_fibre_iff_simple_root`, `Proofs.FibreCount` | The fibres of the gadget are the simple roots of a cubic |
| `image_complex`, `image_real`, `omitted_curve` | The gadget misses one curve and nothing else |
| `cubic_fibre`, `cubicPoly_not_injective` | The 12-variable map of degree 3 has the fibres of the gadget |
| `Proofs.QuadraticKellerMapsAreInjective` | Degree two is injective |
| `hitsTarget_iff_satisfiable` | One map for all formulas: the formula enters only through the target |

Open in Lean, stated in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean): the Jacobian
determinant of the 12-variable map (O4, checked by exact arithmetic), and bijectivity at degree
two (O5).

## Try it

```bash
git clone https://github.com/open-challenges/keller-zero && cd keller-zero
python3 scripts/check_gadget.py submissions/*/gadget.json     # exact, no installs
python3 scripts/lower_degree.py gadget 4                      # the gadget at degree 4, 7 variables
cd lean && lake exe cache get && lake build && cd ..          # Lean through elan
python3 scripts/check_proofs.py
```

## Credit and license

The gadget is Levent Alpöge's map
([announcement](https://x.com/__alpoge__/status/2079028340955197566)); the reduction is Lev
Stambler's ([alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS), MIT); lowering the
degree is the method of Bass, Connell and Wright. The Lean proofs, the findings, the checkers
and the notes were written with Claude. MIT license.

Listed on [Open Challenge List](https://openchallengelist.com).
