# Keller Zero: notes for coding agents

The full rules are in [PROBLEM.md](PROBLEM.md); what is known is in [FINDINGS.md](FINDINGS.md)
and [COMPLEXITY.md](COMPLEXITY.md).

## A smaller gadget (tracks `cubic-variables`, `quartic-variables`, `degree-3d`, `variables`)

Find polynomials `F_1 .. F_N` with rational coefficients whose Jacobian determinant is a nonzero
constant, and two different rational points with the same image. The marks to beat: 11
variables at degree 3, 7 at degree 4, degree 7 in three variables, 3 variables at any degree.

```bash
python3 scripts/check_gadget.py submissions/<handle>/gadget.json    # exact; prints variables and degree
python3 scripts/lower_degree.py gadget 3                            # how the 11-variable map is built
python3 scripts/test_check_gadget.py && python3 scripts/test_lower_degree.py
```

Copy the format from `submissions/alpoge-stambler/gadget.json`. Degree 2 cannot work (proved in
Lean). Two variables would settle the plane Jacobian conjecture, so check such a result twice.

Where to look: `scripts/lower_degree.py` trades degree for variables by adding "wires", and
`lean/KellerZero/Wire.lean` proves that this keeps the determinant and the zeros. Every wire
saved is a record. Search the literature before you claim one: the first version of this
repository claimed a record at degree 3 that was four months old.

## A statement (track `open-statements`)

```bash
cd lean && lake exe cache get && lake build && cd ..    # once; Lean v4.36.0 through elan
python3 scripts/check_proofs.py                         # which statements are proved
```

Open: `O5` and `O7` in `lean/KellerZero/Open.lean`. Add `lean/KellerZero/Proofs/<Name>.lean`
with `theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>`. Do not change the statement:
if it looks false or badly stated, open an issue instead.

- O5 is Wang's theorem. Injectivity is already there
  (`Proofs/QuadraticKellerMapsAreInjective.lean`); surjectivity is the work.
- O7 needs Hensel's lemma in several variables over the `p`-adic integers, which Mathlib has
  only in one variable, and then the Nullstellensatz.

## Entering

Add `submissions/<handle>/SUBMISSION.md` (start from the baseline's) and open a pull request
that touches only your own files. Name the model and harness in its `agent` block.
