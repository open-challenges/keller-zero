# Findings

26 November 2026. Three results found while working on [DIRECTION.md](DIRECTION.md). The labels
are the same as there: **Lean** (proved in [`lean/`](lean), standard axioms only), **Computed**
(exact arithmetic, script named), **Paper** (argued here), **Known** (published; cited from
memory, not re-opened).

None of them is a lower bound. They say what the object is and where its hardness starts.

## 1. The gadget is one cubic in disguise

Write `u = 1 + xy` and `w = 5 - 3u - x²z`. Then, as identities of polynomials (Lean:
`R_eq_mul`, `mul_Q_eq`, `sq_mul_P_eq`),

    R = x w,      x Q = 4u + 2 - 3u² w,      x² P = u² + u - u³ w.

So with `m = u w` the products `QR` and `PR²` depend on `m` and `w` alone, and at every point

    m³ - 2m² + (QR) m - 2 (PR²) = 0,        3m² - 4m + QR = 2w.

For a target `(a, b, c)` call `g(m) = m³ - 2m² + bc·m - 2ac²` its cubic.

| Statement | Lean name | Label |
|---|---|---|
| If `c ≠ 0`: `(a, b, c)` is a value of the gadget exactly when `g` has a simple root in the field. Any field of characteristic zero | `mem_fibre_iff_simple_root` | Lean |
| If `c ≠ 0`, over ℂ: the fibre has exactly as many points as `g` has simple roots, so three, one or none | `Proofs.FibreCount` | Lean |
| If `c = 0`: `(a, b, 0)` is always a value | `value_of_c_eq_zero` | Lean |
| `g` has no simple root over an algebraically closed field exactly when `g = (m - 2/3)³`, and that is the curve `(t²/12, t, 4/(3t))` | `simple_root_or_triple`, `on_curve_of_triple` | Lean |
| Over ℂ the gadget takes every value off the curve and none on it | `image_complex` (this was O1) | Lean |
| The same over ℝ: a real cubic has a real root | `image_real` | Lean |
| Scaling `(x, y, z) → (λx, y/λ, z/λ²)` sends the value to `(P/λ², Q/λ, λR)`; the curve is one orbit | `scaling` | Lean |

What this explains:

- **The omitted curve is the triple-root locus.** The one target Stambler's reduction needs,
  `(7, 24, 8)`, is a point where three preimages have collided and left.
- **Why three.** The generic fibre has three points because the map is a cubic. A fibre of
  size two cannot occur generically: a Keller map whose field extension is Galois is
  invertible (Known: Campbell, 1973), and every extension of degree two is Galois.
- **Why degree 7.** On the quotient by the scaling, the map is
  `(m, w) ↦ (4m - 3m² + 2w, m² - m³ + mw)`, the universal unfolding of a cubic, of degree 3 and
  with Jacobian determinant `-2w`. The gadget is that map after substituting `m = uw` and
  lifting to three variables; the term `u³w` of `x²P` has degree 9 in `x, y, z`, hence degree 7
  for `P` (Paper).
- **Over ℚ the image is thin.** A rational target with `c ≠ 0` is a value over ℚ exactly when
  its cubic has a simple rational root (Lean, the first row with the field ℚ).

## 2. NP-hardness starts at degree 3, and that is the lowest it can start

**Degree 2 is trivial.** A polynomial map of degree at most two with constant nonzero Jacobian
determinant is injective (Lean: `Proofs.QuadraticKellerMapsAreInjective`, this was O3; the
midpoint argument). It is in fact a bijection with a polynomial inverse (Known: Wang, 1980;
open in Lean as O5), so the answer to "is there a zero?" is always yes.

**Degree 3 is NP-hard.** There is a polynomial map in 12 variables, of degree 3 with integer
coefficients, whose Jacobian determinant is the constant `-2` and which takes the same value at
two rational points: [`submissions/SecurityQQ/gadget.json`](submissions/SecurityQQ/gadget.json).

| Fact about the 12-variable map | Label |
|---|---|
| Jacobian determinant `-2`, degree 3, two points with one value | Computed: `scripts/check_gadget.py`, exact rational arithmetic; the determinant also agrees with a second implementation at 60 random rational points |
| A target `(a, b, c, 0, …, 0)` is a value exactly when `(a, b, c)` is a value of the gadget; the map is not injective | Lean: `cubic_fibre`, `cubicPoly_not_injective` |
| Jacobian determinant `-2`, in Lean | open: O4 |

Replacing every block of Stambler's map by this one, and the product of three literal values by
three more variables per clause, gives a map of degree 3 in `12n + 15m` variables with constant
Jacobian determinant and a zero exactly when the formula is satisfiable.

| Fact about the map of the reduction at degree 3 | Label |
|---|---|
| The construction and why it keeps the fibres | Paper: the header of [`scripts/lower_degree.py`](scripts/lower_degree.py) |
| For two formulas (54 and 69 variables): degree 3, Jacobian determinant `(-3456)^(n+m)`, a zero above a satisfying assignment, none above a falsifying one at any choice of witnesses | Computed: `scripts/test_lower_degree.py` |
| For every formula, in Lean | not stated yet |

So the zero problem for maps with constant Jacobian determinant is trivial at degree 2 and
NP-hard at degree 3. Degree 3 is also where the Jacobian conjecture has always been known to
live: Bass, Connell and Wright (1982) reduced it to maps of degree 3. Their reduction is the
method used here, so that a counterexample of degree 3 exists in some dimension follows from
theirs at once. What is new is an explicit one in 12 variables, checked exactly, and the
observation that the reduction costs a constant number of variables per block, so the
NP-hardness survives it.

**The method.** Given `F` in the variables `x`, add variables `t₁ … t_r` and "wires"
`wireᵢ = tᵢ + lᵢ(x, t₁ … tᵢ₋₁) + qᵢ(wire₁ … wireᵢ₋₁)`, and output
`G = (F - p(wires), tᵢ + lᵢ)`. Then `G = T ∘ (F × id) ∘ S` for two triangular maps `S` and `T`,
so `det JG = det JF` and `G` has the fibres of `F`. The work is choosing `l`, `q`, `p` so that
every coordinate has degree at most 3. For the gadget, with `E = uz + 3y²`:
`P = u²E + uy²` and `Q = y + 3xy² + 3(xu)E`, and nine wires suffice.

**The trade between variables and degree** (Computed, `python3 scripts/lower_degree.py gadget d`):

| Degree | 7 | 6 | 5 | 4 | 3 | 2 |
|---|---|---|---|---|---|---|
| Variables | 3 | 5 | 6 | 7 | 12 | impossible |

Nothing says these are optimal except the last column.

## 3. Stambler's theorem is machine-checked from end to end

O2 is proved (`Proofs.ReductionMapIsKeller`: the Jacobian matrix is block triangular once the
clause blocks are put first). Together with the zero statement, one Lean theorem now says it
all (`threeSAT_reduces_to_keller_zero` in [`lean/KellerZero/Summary.lean`](lean/KellerZero/Summary.lean)):

> For every 3CNF formula `φ` with `n` variables and `m` clauses, `reductionMap φ` is a map of
> `3n + 3m` integer polynomials whose Jacobian determinant is `(-3456)^(n+m)`, and over every
> field of characteristic zero it has a zero exactly when `φ` is satisfiable.

## What is still open here

- O4, O5 in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean): the determinant of the
  12-variable map in Lean; bijectivity at degree 2 in Lean.
- Fewer than 12 variables at degree 3. Fewer than 7 at degree 4, and so on. Degree below 7 in
  three variables.
- The reduction at degree 3 as a Lean theorem for every formula.
- Everything in section 4 of DIRECTION.md: the missing link to a lower bound is untouched.

## What was not checked

- Whether any of this is already in print or in the discussion after the announcement. No
  literature search was made.
- Which pairs (variables, degree) are known to be impossible, beyond degree 2 and one variable.
