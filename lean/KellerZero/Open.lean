import KellerZero.Reduction
import Mathlib.Analysis.Complex.Basic

/-!
# Open statements

Each `def ... : Prop` below is a statement nobody has checked in this repository yet. To enter
the `checked` track, add a file under `KellerZero/Proofs/` that proves one of them exactly as
stated (`theorem ... : KellerZero.Open.<Name> := ...`), with no `sorry` and no new axiom.

Nothing in this file is assumed anywhere: these are definitions of propositions, not axioms.
What is already proved about each one is stated next to it.
-/

namespace KellerZero.Open

open KellerZero

open MvPolynomial

/-! ## O1. The image of the gadget over the complex numbers -/

/-- O1. Over the complex numbers the gadget misses the curve of `omitted_curve` and nothing
else. Computer algebra (a resultant, then spot checks with Gröbner bases) says yes. -/
def ImageIsComplementOfCurve : Prop :=
  ∀ a b c : ℂ, (∃ x y z : ℂ, P x y z = a ∧ Q x y z = b ∧ R x y z = c) ↔
    ¬ ∃ t : ℂ, t ≠ 0 ∧ a = t ^ 2 / 12 ∧ b = t ∧ c = 4 / (3 * t)

/-- The half of O1 that is checked: a value of the gadget is never on the curve. -/
theorem image_subset (a b c : ℂ) (h : ∃ x y z : ℂ, P x y z = a ∧ Q x y z = b ∧ R x y z = c) :
    ¬ ∃ t : ℂ, t ≠ 0 ∧ a = t ^ 2 / 12 ∧ b = t ∧ c = 4 / (3 * t) := by
  rintro ⟨t, ht, ha, hb, hc⟩
  obtain ⟨x, y, z, hP, hQ, hR⟩ := h
  exact omitted_curve t ht x y z ⟨hP.trans ha, hQ.trans hb, hR.trans hc⟩

/-! ## O2. The map of the reduction is a Keller map -/

/-- O2. The Jacobian determinant of the map of the reduction is the constant
`(-3456) ^ (n + m)`. On paper: the Jacobian matrix is block lower triangular with a copy of the
gadget's Jacobian in every diagonal block. -/
def ReductionMapIsKeller : Prop :=
  ∀ (n m : ℕ) (φ : Fin m → Clause n),
    (Matrix.of fun a b => pderiv b (reductionMap φ a)).det = C ((-3456) ^ (n + m))

/-! ## O3. The floor of the degree track -/

/-- O3. A polynomial map of degree at most two whose Jacobian determinant is a nonzero constant
is injective (Wang, 1980). So no entry of the `degree` track can go below three. On paper: if
`F a = F b` with `a ≠ b`, the quadratic `t ↦ F (a + t (b - a))` takes the same value at `0` and
`1`, so its derivative at `1/2` vanishes, and the Jacobian at the midpoint kills `b - a`. -/
def QuadraticKellerMapsAreInjective : Prop :=
  ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℚ), (∀ i, (F i).totalDegree ≤ 2) →
    IsUnit (Matrix.of fun i j => pderiv j (F i)).det →
    Function.Injective fun v : Fin N → ℚ => fun i => eval v (F i)

end KellerZero.Open
