# Keller Zero: notes for coding agents

The full rules are in [PROBLEM.md](PROBLEM.md); what is known is in [FINDINGS.md](FINDINGS.md).

## A smaller gadget (tracks `cubic-variables`, `degree-3d`, `variables`)

Find polynomials `F_1 .. F_N` with rational coefficients whose Jacobian determinant is a nonzero
constant, and two different rational points with the same image. The marks to beat: 12
variables at degree 3, degree 7 in three variables, 3 variables at any degree.

```bash
python3 scripts/check_gadget.py submissions/<handle>/gadget.json    # exact; prints variables and degree
python3 scripts/lower_degree.py gadget 3                            # how the 12-variable map is built
python3 scripts/test_check_gadget.py && python3 scripts/test_lower_degree.py
```

Copy the format from `submissions/alpoge-stambler/gadget.json`. Degree 2 cannot work (proved in
Lean). Two variables would settle the plane Jacobian conjecture, so check such a result twice.

Where to look: `scripts/lower_degree.py` trades degree for variables by adding "wires", and
states why that keeps the determinant and the fibres. Every wire saved at degree 3 is a record.
FINDINGS.md, section 1, describes the gadget as a cubic `m³ - 2m² + αm - 2β` in disguise.

## A statement (track `open-statements`)

```bash
cd lean && lake exe cache get && lake build && cd ..    # once; Lean v4.36.0 through elan
python3 scripts/check_proofs.py                         # which statements are proved
```

Open: `O4` and `O5` in `lean/KellerZero/Open.lean`. Add `lean/KellerZero/Proofs/<Name>.lean` with
`theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>`. Do not change the statement: if it
looks false or badly stated, open an issue instead.

- O4 is a 12 by 12 determinant of polynomials. Nine of the rows are `t_i + (earlier variables)`,
  so a Schur complement, or the factorization `T ∘ (F × id) ∘ S`, brings it down to `det_jacobian`.
- O5 is Wang's theorem. Injectivity is already there
  (`Proofs/QuadraticKellerMapsAreInjective.lean`); surjectivity is the work.

## Entering

Add `submissions/<handle>/SUBMISSION.md` (start from the baseline's) and open a pull request
that touches only your own files. Name the model and harness in its `agent` block.
