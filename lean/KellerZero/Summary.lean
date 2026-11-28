import KellerZero.Proofs.ImageIsComplementOfCurve
import KellerZero.Proofs.ReductionMapIsKeller
import KellerZero.Proofs.QuadraticKellerMapsAreInjective
import KellerZero.CubicReduction

/-!
# The reduction, in one statement

For every 3CNF formula `φ` with `n` variables and `m` clauses, `reductionMap φ` is a map of
`3 n + 3 m` polynomials with integer coefficients in as many variables such that

* its Jacobian determinant is the nonzero constant `(-3456) ^ (n + m)`, and
* over every field of characteristic zero it has a zero exactly when `φ` is satisfiable.

This is the theorem of L. Stambler, *Reducing 3SAT to Zero-Finding for Constant-Jacobian
Polynomial Maps* (2026), with the gadget of L. Alpöge.

The same at degree three, the least degree at which it can hold, is
`threeSAT_reduces_to_cubic_keller_zero` in `CubicReduction.lean`: `10 n + 13 m` variables. A
smaller map with the same properties, `10 n + ⌈m / 2⌉ + 12` variables, is
`threeSAT_reduces_with_one_checker` in `CompactReduction.lean`.
`keller_zero_hard_exactly_from_degree_three` below puts the two halves side by side.
-/

namespace KellerZero

open MvPolynomial

theorem threeSAT_reduces_to_keller_zero {n m : ℕ} (φ : Fin m → Clause n) :
    (Matrix.of fun a b => pderiv b (reductionMap φ a)).det = C ((-3456) ^ (n + m)) ∧
      ∀ (K : Type) [Field K] [CharZero K],
        (∃ u : Var n m → K, ∀ a, aeval u (reductionMap φ a) = 0) ↔
          ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ :=
  ⟨Proofs.ReductionMapIsKeller n m φ, fun _ _ _ => exists_zero_reductionMap_iff_satisfiable φ⟩

/-- The zero problem is trivial at degree two and NP-hard at degree three: a map of degree at
most two with constant nonzero Jacobian determinant is injective, and every 3CNF formula has a
map of degree at most three with constant nonzero Jacobian determinant that has a rational zero
exactly when the formula is satisfiable. -/
theorem keller_zero_hard_exactly_from_degree_three :
    (∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℚ), (∀ i, (F i).totalDegree ≤ 2) →
      IsUnit (Matrix.of fun i j => pderiv j (F i)).det →
      Function.Injective fun v : Fin N → ℚ => fun i => eval v (F i)) ∧
    ∀ (n m : ℕ) (φ : Fin m → Clause n),
      (∀ a, (cubicReduction φ a).totalDegree ≤ 3) ∧
      (Matrix.of fun a b => pderiv b (cubicReduction φ a)).det = C ((-3456) ^ (n + m)) ∧
      ((∃ v : Var3 n m → ℚ, ∀ a, aeval v (cubicReduction φ a) = 0) ↔
        ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ) :=
  ⟨Proofs.QuadraticKellerMapsAreInjective, fun _ _ φ =>
    ⟨totalDegree_cubicReduction φ, det_cubicReduction φ,
      exists_zero_cubicReduction_iff_satisfiable φ⟩⟩

end KellerZero
