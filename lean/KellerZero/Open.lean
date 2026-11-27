import KellerZero.Reduction
import KellerZero.Structure
import KellerZero.Cubic
import KellerZero.Refutation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Statements to prove

Each `def ... : Prop` below is a statement put up to be proved. To enter the `open-statements`
track, add `KellerZero/Proofs/<Name>.lean` proving one of them exactly as stated
(`theorem KellerZero.Proofs.<Name> : KellerZero.Open.<Name>`), with no `sorry` and no new axiom.

Nothing in this file is assumed anywhere: these are definitions of propositions, not axioms.

| | Statement | Status |
|---|---|---|
| O1 | `ImageIsComplementOfCurve` | proved, `Proofs/ImageIsComplementOfCurve.lean` |
| O2 | `ReductionMapIsKeller` | proved, `Proofs/ReductionMapIsKeller.lean` |
| O3 | `QuadraticKellerMapsAreInjective` | proved, `Proofs/QuadraticKellerMapsAreInjective.lean` |
| O4 | `CubicGadgetIsKeller` | proved, `Proofs/CubicGadgetIsKeller.lean` |
| O5 | `QuadraticKellerMapsAreBijective` | open in Lean (Wang, 1980) |
| O6 | `FibreCount` | proved, `Proofs/FibreCount.lean` |
| O7 | `WitnessIsSound` | open in Lean (Hensel's lemma and the Nullstellensatz; COMPLEXITY.md, Theorem 2) |
| O8 | `RefutationOfMap` | open in Lean (proved on paper in COMPLEXITY.md, Theorem 5 (b)) |
-/

namespace KellerZero.Open

open KellerZero

open MvPolynomial

/-! ## O1. The image of the gadget over the complex numbers -/

/-- O1. Over the complex numbers the gadget misses the curve of `omitted_curve` and nothing
else. -/
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

/-! ## O4. The gadget at degree three is a Keller map -/

/-- O4. The Jacobian determinant of the twelve-variable map of degree three is the constant
`-2`. Exact rational arithmetic says so (`scripts/check_gadget.py`), and on paper the map is the
gadget composed with two triangular maps. Proved through `KellerZero.Wire`: the map is a wire
extension of the gadget. -/
def CubicGadgetIsKeller : Prop :=
  (Matrix.of fun i j => pderiv j (cubicPoly ℤ i)).det = C (-2)

/-! ## O5. Degree two: not only injective -/

/-- O5. A polynomial map of degree at most two whose Jacobian determinant is a nonzero constant
is a bijection (Wang, 1980: it has a polynomial inverse). With O3 this says that the question
"is there a zero?" has the answer yes, exactly one, at degree two. -/
def QuadraticKellerMapsAreBijective : Prop :=
  ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℚ), (∀ i, (F i).totalDegree ≤ 2) →
    IsUnit (Matrix.of fun i j => pderiv j (F i)).det →
    Function.Bijective fun v : Fin N → ℚ => fun i => eval v (F i)

/-! ## O6. Counting the fibre -/

/-- O6. Over the complex numbers, a target `(a, b, c)` with `c ≠ 0` has exactly as many
preimages under the gadget as its cubic has simple roots: three, one or none.
`mem_fibre_iff_simple_root` is the statement that one set is empty exactly when the other is. -/
def FibreCount : Prop :=
  ∀ a b c : ℂ, c ≠ 0 →
    Set.ncard {p : ℂ × ℂ × ℂ | P p.1 p.2.1 p.2.2 = a ∧ Q p.1 p.2.1 p.2.2 = b ∧ R p.1 p.2.1 p.2.2 = c}
      = Set.ncard {m : ℂ | cubic a b c m = 0 ∧ cubicDeriv b c m ≠ 0}

/-! ## O7. A zero modulo a prime proves a complex zero -/

/-- O7. If a square system of integer polynomials has a zero modulo a prime `p` at which its
Jacobian determinant is not zero modulo `p`, then it has a complex zero. On paper: Hensel's
lemma lifts the zero to the `p`-adic integers, so the system has a solution in a field of
characteristic zero, and then, by the Nullstellensatz, a complex one. This is what makes "does a
map with constant Jacobian determinant have a complex zero?" a problem with short proofs. -/
def WitnessIsSound : Prop :=
  ∀ (N p : ℕ) (_ : Fact p.Prime) (F : Fin N → MvPolynomial (Fin N) ℤ) (a : Fin N → ZMod p),
    (∀ i, aeval a (F i) = 0) →
    (Matrix.of fun i j => aeval a (pderiv j (F i))).det ≠ 0 →
    ∃ x : Fin N → ℂ, ∀ i, aeval x (F i) = 0

/-! ## O8. A refutation of the formula gives a refutation of its map -/

/-- O8. The converse of `refutation_of_formula`, up to a constant: a Nullstellensatz refutation
of degree `d` of the equations of a formula gives one of degree at most `2 d + c` of the
equations of its map. On paper `c = 18` works: substitute the square of the first variable of
every block, and use `quartic_certificate` and `target_certificate`. -/
def RefutationOfMap : Prop :=
  ∃ c : ℕ, ∀ (n m : ℕ) (φ : Fin m → Clause n) (d : ℕ),
    NSRefutation (formulaAxioms φ) d → NSRefutation (kellerAxioms φ) (2 * d + c)

end KellerZero.Open
