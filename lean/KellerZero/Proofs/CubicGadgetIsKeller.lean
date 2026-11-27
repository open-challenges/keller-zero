import KellerZero.Open
import KellerZero.Wire

/-!
# O4: the twelve-variable map of degree three has Jacobian determinant `-2`

The map is a wire extension of the gadget (`KellerZero.Wire`): nine wires, each its own variable
plus a polynomial in `x, y, z` and earlier wires, and the three coordinates of the gadget minus
polynomials in the wires. So its Jacobian determinant is the gadget's.
-/

namespace KellerZero.Proofs.Cubic12

open MvPolynomial KellerZero

/-- The twelve variables as `x, y, z` and nine wires. -/
def idx : Fin 3 ⊕ Fin 9 → Fin 12 := Sum.elim ![0, 1, 2] ![3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem idx_bijective : Function.Bijective idx := by decide

/-- The same as an equivalence. -/
noncomputable def idxEquiv : Fin 3 ⊕ Fin 9 ≃ Fin 12 := Equiv.ofBijective idx idx_bijective

local notation "x₀" => (X (Sum.inl 0) : MvPolynomial (Fin 3 ⊕ Fin 9) ℤ)
local notation "y₀" => (X (Sum.inl 1) : MvPolynomial (Fin 3 ⊕ Fin 9) ℤ)
local notation "z₀" => (X (Sum.inl 2) : MvPolynomial (Fin 3 ⊕ Fin 9) ℤ)
local notation "t" i => (X (Sum.inr i) : MvPolynomial (Fin 3 ⊕ Fin 9) ℤ)

/-- The nine wires. -/
noncomputable def wires : Fin 9 → MvPolynomial (Fin 3 ⊕ Fin 9) ℤ :=
  ![(t 0) + x₀ * y₀,
    (t 1) + x₀ + x₀ ^ 2 * y₀,
    (t 2) + z₀ + 3 * y₀ ^ 2 + x₀ * y₀ * z₀,
    (t 3) + 3 * z₀ * (t 1) + 3 * x₀ * (t 2),
    (t 4) - (t 0) ^ 2 - 2 * x₀ * y₀ * (t 0),
    (t 5) + x₀ * y₀ * (t 2),
    (t 6) - (t 0) * (t 2) + z₀ * (t 4) + 2 * z₀ * (t 0) - y₀ ^ 2,
    (t 7) + x₀ ^ 2,
    (t 8) + x₀ * z₀]

/-- What the wires carry away from the three coordinates of the gadget. -/
noncomputable def carried : Fin 3 → MvPolynomial (Fin 9) ℤ :=
  ![2 * X 0 * X 2 + (X 4 + X 0 ^ 2) * X 2 - X 0 * X 5 - X 0 * X 6,
    3 * X 1 * X 2 - X 0 * X 3,
    -(X 7 * X 8)]

theorem pderiv_wires_self (w : Fin 9) : pderiv (Sum.inr w) (wires w) = 1 := by
  fin_cases w <;> simp [wires, pderiv_ofNat]

theorem pderiv_wires_of_lt (w w' : Fin 9) (h : w < w') : pderiv (Sum.inr w') (wires w) = 0 := by
  fin_cases w <;> fin_cases w' <;>
    first
      | exact absurd h (by decide)
      | simp [wires, pderiv_ofNat]

/-- The twelve-variable map is the wire extension, in the variables `idx`. -/
theorem cubicPoly_eq (a : Fin 3 ⊕ Fin 9) :
    cubicPoly ℤ (idx a) = rename idx (wireExt (poly ℤ) wires carried a) := by
  rcases a with k | w
  · fin_cases k <;> simp [wireExt, poly, wires, carried, cubicPoly, idx, map_ofNat] <;> ring
  · fin_cases w <;> simp [wireExt, wires, cubicPoly, idx, map_ofNat]

end KellerZero.Proofs.Cubic12

open KellerZero.Proofs.Cubic12 MvPolynomial in
theorem KellerZero.Proofs.CubicGadgetIsKeller : KellerZero.Open.CubicGadgetIsKeller := by
  unfold KellerZero.Open.CubicGadgetIsKeller
  have hdet := det_wireExt (poly ℤ) wires carried (fun w => (w : ℕ)) pderiv_wires_self
    (fun c d hcd hle => pderiv_wires_of_lt c d (lt_of_le_of_ne hle hcd))
  have hJ := det_jacobian ℤ
  rw [jacobian] at hJ
  rw [hJ, rename_C] at hdet
  have hsub : (Matrix.of fun i j => pderiv j (cubicPoly ℤ i)).submatrix idxEquiv idxEquiv
      = (rename (R := ℤ) idx).toRingHom.mapMatrix
        (Matrix.of fun a b => pderiv b (wireExt (poly ℤ) wires carried a)) := by
    refine Matrix.ext fun a b => ?_
    have h := pderiv_rename (R := ℤ) idx_bijective.injective b (wireExt (poly ℤ) wires carried a)
    simp only [Matrix.submatrix_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    change pderiv (idx b) (cubicPoly ℤ (idx a)) = _
    rw [cubicPoly_eq, h]
    rfl
  rw [← Matrix.det_submatrix_equiv_self idxEquiv, hsub, ← RingHom.map_det, hdet]
  exact rename_C idx (-2)
