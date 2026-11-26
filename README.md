# Keller Zero

**3SAT reduces to finding a zero of a polynomial map with constant Jacobian.** This repository
checks that chain in Lean, and asks how small the gadget behind it can be.

In July 2026 Levent Alpöge announced an explicit polynomial map in three variables whose
Jacobian determinant is constant and which is not injective, a counterexample to the Jacobian
conjecture. Lev Stambler [turned it into a reduction](https://github.com/Lev-Stambler/alg-geom-TCS):
a 3CNF formula becomes a polynomial map with constant Jacobian that has a zero exactly when the
formula is satisfiable. A question conjectured to have the same answer every time is NP-hard.

- [PROBLEM.md](PROBLEM.md): the tracks, the rules, how to enter.
- [DIRECTION.md](DIRECTION.md): the research direction, with what is proved, what is computed and
  what is open, and how far it goes toward P vs NP.
- [AGENTS.md](AGENTS.md): the short version for coding agents.

## Leaderboard

| Track | Record | Entry | Date |
|---|---|---|---|
| `degree`: lowest degree of a gadget | 7 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `variables`: fewest variables of a gadget | 3 (baseline) | [Alpöge's map, as used by Stambler](submissions/alpoge-stambler/SUBMISSION.md) | 2026-11-26 |
| `open-statements`: open statements proved | 0 of 3 | none yet | |

Degree 2 is impossible, and an entry with 2 variables would settle the plane Jacobian
conjecture.

## Checked in Lean

Lean v4.36.0, Mathlib `fc4f59e5`, axioms `propext`, `Classical.choice`, `Quot.sound` only.
CI rebuilds everything on every push.

| Theorem ([`lean/KellerZero`](lean/KellerZero)) | Says |
|---|---|
| `det_jacobian` | The Jacobian determinant of the gadget is -2 |
| `jacobian_conjecture_fails_dim_three` | A map with constant Jacobian determinant that is not injective, over every field of characteristic zero |
| `fibre_zero` | The gadget takes the value (-1/4, 0, 0) at exactly three points |
| `omitted_curve` | The gadget never takes a value (t²/12, t, 4/(3t)), t ≠ 0 |
| `exists_zero_reductionMap_iff_satisfiable` | The map built from a formula has a zero exactly when the formula is satisfiable |
| `hitsTarget_iff_satisfiable` | One map for all formulas: the formula enters only through the target |

Open, stated in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean): the gadget misses
nothing but the curve (O1), the map of the reduction has constant Jacobian determinant (O2),
and maps of degree two are injective (O3).

## Try it

```bash
git clone https://github.com/open-challenges/keller-zero && cd keller-zero
python3 scripts/check_gadget.py submissions/alpoge-stambler/gadget.json   # exact, no installs
cd lean && lake exe cache get && lake build && cd ..                      # Lean through elan
python3 scripts/check_proofs.py
```

## Credit and license

The gadget is Levent Alpöge's map
([announcement](https://x.com/__alpoge__/status/2079028340955197566)); the reduction is Lev
Stambler's ([alg-geom-TCS](https://github.com/Lev-Stambler/alg-geom-TCS), MIT). The Lean proofs,
the checkers and the note were written with Claude. MIT license.

Listed on [Open Challenge List](https://openchallengelist.com).
