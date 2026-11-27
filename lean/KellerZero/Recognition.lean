import KellerZero.Wire
import KellerZero.Degree

/-!
# Recognising a map with constant Jacobian determinant is identity testing

For a square matrix `M` of polynomials in the variables `x`, the map

    (x, y) ↦ (x, M(x) y)

has Jacobian determinant `det M(x)` (`det_jacobian_bilinearMap`). If the entries of `M` have
degree at most one, the map has degree at most two (`totalDegree_bilinearMap`). So the question
"is the Jacobian determinant of this map of degree two a nonzero constant?" contains the question
"is the determinant of this matrix of linear forms a nonzero constant?", which is polynomial
identity testing for symbolic determinants. See COMPLEXITY.md for the reductions in both
directions.
-/

namespace KellerZero

open MvPolynomial

variable {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

/-- The map `(x, y) ↦ (x, M(x) y)`. -/
noncomputable def bilinearMap (M : Matrix β β (MvPolynomial α R)) :
    α ⊕ β → MvPolynomial (α ⊕ β) R :=
  Sum.elim (fun i => X (Sum.inl i)) (fun b => ∑ c, rename Sum.inl (M b c) * X (Sum.inr c))

/-- The Jacobian determinant of `(x, y) ↦ (x, M(x) y)` is `det M(x)`. -/
theorem det_jacobian_bilinearMap (M : Matrix β β (MvPolynomial α R)) :
    (Matrix.of fun a b => pderiv b (bilinearMap M a)).det = rename Sum.inl M.det := by
  set D : Matrix β β (MvPolynomial (α ⊕ β) R) := Matrix.of fun b c => rename Sum.inl (M b c)
    with hD
  set Cb : Matrix β α (MvPolynomial (α ⊕ β) R) :=
    Matrix.of fun b k => pderiv (Sum.inl k) (bilinearMap M (Sum.inr b)) with hC
  have hM : (Matrix.of fun a b => pderiv b (bilinearMap M a)) = Matrix.fromBlocks 1 0 Cb D := by
    ext (i | b) (k | c)
    · simp [bilinearMap, Matrix.one_apply, Pi.single_apply]
    · simp [bilinearMap]
    · simp [hC]
    · simp [bilinearMap, hD, pderiv_inr_rename_inl, Pi.single_apply]
  have hDdet : D.det = rename Sum.inl M.det := by
    have : D = (rename (R := R) (Sum.inl : α → α ⊕ β)).toRingHom.mapMatrix M := by
      ext b c
      simp [hD]
    rw [this, ← RingHom.map_det]
    rfl
  rw [hM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, hDdet]

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- If the entries of `M` have degree at most one, the map has degree at most two. -/
theorem totalDegree_bilinearMap [Nontrivial R] (M : Matrix β β (MvPolynomial α R))
    (hM : ∀ b c, (M b c).totalDegree ≤ 1) (a : α ⊕ β) : (bilinearMap M a).totalDegree ≤ 2 := by
  rcases a with i | b
  · exact (Deg.var _).trans (by norm_num)
  · refine totalDegree_finsetSum_le fun c _ => ?_
    exact (Deg.mul (Deg.rename _ (hM b c)) (Deg.var _)).trans (by norm_num)

end KellerZero
