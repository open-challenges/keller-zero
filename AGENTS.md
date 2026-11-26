# Keller Zero: notes for coding agents

Three ways to score; the full rules are in [PROBLEM.md](PROBLEM.md), the mathematics in
[DIRECTION.md](DIRECTION.md).

## A smaller gadget (tracks `degree`, `variables`)

Find polynomials `F_1 .. F_N` with rational coefficients whose Jacobian determinant is a nonzero
constant, and two different rational points with the same image. Beat degree 7 or 3 variables.

```bash
python3 scripts/check_gadget.py submissions/<handle>/gadget.json    # exact; prints the scores
python3 scripts/test_check_gadget.py                                # the checker's own tests
```

Copy the format from `submissions/alpoge-stambler/gadget.json`. Degree 2 cannot work. Two
variables would settle the plane Jacobian conjecture, so check such a result twice.

## An open statement (track `open-statements`)

```bash
cd lean && lake exe cache get && lake build && cd ..    # once; Lean v4.36.0 through elan
python3 scripts/check_proofs.py                         # which open statements are proved
```

Pick `O1`, `O2` or `O3` in `lean/KellerZero/Open.lean`. Add `lean/KellerZero/Proofs/<Name>.lean`
with `theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>`. Do not change the statement:
if it looks false or badly stated, open an issue instead.

- O3 is the shortest on paper (a quadratic that agrees at 0 and 1 has zero derivative at 1/2).
- O2 is linear algebra: `Matrix.BlockTriangular` and the determinant of the gadget, `det_jacobian`.
- O1 needs roots of a cubic over the complex numbers; `scripts/omitted_set.py` shows the route.

## Entering

Add `submissions/<handle>/SUBMISSION.md` (start from the baseline's) and open a pull request
that touches only your own files. Name the model and harness in its `agent` block.
