import KellerZero.Proofs.ImageIsComplementOfCurve
import KellerZero.Proofs.ReductionMapIsKeller
import KellerZero.Proofs.QuadraticKellerMapsAreInjective

/-!
# The reduction, in one statement

For every 3CNF formula `φ` with `n` variables and `m` clauses, `reductionMap φ` is a map of
`3 n + 3 m` polynomials with integer coefficients in as many variables such that

* its Jacobian determinant is the nonzero constant `(-3456) ^ (n + m)`, and
* over every field of characteristic zero it has a zero exactly when `φ` is satisfiable.

This is the theorem of L. Stambler, *Reducing 3SAT to Zero-Finding for Constant-Jacobian
Polynomial Maps* (2026), with the gadget of L. Alpöge.
-/

namespace KellerZero

open MvPolynomial

theorem threeSAT_reduces_to_keller_zero {n m : ℕ} (φ : Fin m → Clause n) :
    (Matrix.of fun a b => pderiv b (reductionMap φ a)).det = C ((-3456) ^ (n + m)) ∧
      ∀ (K : Type) [Field K] [CharZero K],
        (∃ u : Var n m → K, ∀ a, aeval u (reductionMap φ a) = 0) ↔
          ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ :=
  ⟨Proofs.ReductionMapIsKeller n m φ, fun _ _ _ => exists_zero_reductionMap_iff_satisfiable φ⟩

end KellerZero
