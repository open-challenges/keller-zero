import KellerZero.Open
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# O2: the map of the reduction has constant Jacobian determinant

Order the blocks with the clauses first and the variables after them. A coordinate of a variable
block involves only its own three variables, and a coordinate of a clause block involves its own
three variables and variables of variable blocks. So the Jacobian matrix is block triangular,
and each diagonal block is the Jacobian matrix of the gadget `H = 12 F + (3, 0, 0)` in the
block's own variables, with determinant `12 ^ 3 * (-2) = -3456`.
-/

namespace KellerZero.Proofs.Keller

open MvPolynomial KellerZero

variable {n m : ℕ}

/-- The number of the block of a variable: clauses first, then variables. -/
def blockOf (a : Var n m) : Fin (m + n) :=
  match a.1 with
  | Sum.inl i => Fin.natAdd m i
  | Sum.inr j => Fin.castAdd n j

theorem rename_block_injective (b : Fin n ⊕ Fin m) :
    Function.Injective fun j : Fin 3 => ((b, j) : Var n m) :=
  fun _ _ h => (Prod.mk.inj h).2

theorem pderiv_three (a : Var n m) (i : Fin 3) :
    pderiv a ((![3, 0, 0] : Fin 3 → MvPolynomial (Var n m) ℤ) i) = 0 := by
  fin_cases i <;> simp [KellerZero.pderiv_ofNat]

theorem pderiv_target (a : Var n m) (i : Fin 3) :
    pderiv a ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) i) = 0 := by
  fin_cases i <;> simp [KellerZero.pderiv_ofNat]

/-- A coordinate of the gadget in block `b` does not involve the variables of another block. -/
theorem pderiv_gadgetAt_of_ne (b b' : Fin n ⊕ Fin m) (h : b' ≠ b) (i j : Fin 3) :
    pderiv ((b', j) : Var n m) (gadgetAt b i) = 0 := by
  have hren : pderiv ((b', j) : Var n m) (rename (fun j => ((b, j) : Var n m)) (poly ℤ i)) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hmem
    have := (vars_rename _ _) hmem
    simp only [Finset.mem_image] at this
    obtain ⟨c, -, hc⟩ := this
    exact h (Prod.mk.inj hc).1.symm
  unfold gadgetAt
  rw [map_add, pderiv_mul, hren, pderiv_three, KellerZero.pderiv_ofNat]
  simp

/-- In its own block, the derivatives of the gadget are those of the gadget, times 12. -/
theorem pderiv_gadgetAt_self (b : Fin n ⊕ Fin m) (i j : Fin 3) :
    pderiv ((b, j) : Var n m) (gadgetAt b i)
      = 12 * rename (fun j => ((b, j) : Var n m)) (pderiv j (poly ℤ i)) := by
  have hren := pderiv_rename (R := ℤ) (rename_block_injective (n := n) (m := m) b) j (poly ℤ i)
  unfold gadgetAt
  rw [map_add, pderiv_mul, hren, pderiv_three, KellerZero.pderiv_ofNat]
  simp

/-- The satisfaction polynomial of a clause involves no variable of a clause block. -/
theorem pderiv_clausePoly (c : Clause n) (j0 : Fin m) (j : Fin 3) :
    pderiv ((Sum.inr j0, j) : Var n m) (clausePoly (m := m) c) = 0 := by
  have hlit : ∀ l : Literal n, pderiv ((Sum.inr j0, j) : Var n m) (literalPoly (m := m) l) = 0 := by
    intro l
    unfold literalPoly
    split_ifs <;> simp [pderiv_X]
  simp [clausePoly, Fin.prod_univ_three, hlit]

/-- The Jacobian matrix of the map of the reduction. -/
noncomputable def jac (φ : Fin m → Clause n) : Matrix (Var n m) (Var n m) (MvPolynomial (Var n m) ℤ) :=
  Matrix.of fun a b => pderiv b (reductionMap φ a)

theorem blockTriangular (φ : Fin m → Clause n) : (jac φ).BlockTriangular blockOf := by
  rintro ⟨b, i⟩ ⟨b', j⟩ hlt
  simp only [jac, Matrix.of_apply]
  rcases b with i0 | j0
  · -- a variable block: every block before it is another block
    have hne : b' ≠ Sum.inl i0 := by
      rintro rfl
      exact lt_irrefl _ hlt
    simpa [reductionMap] using pderiv_gadgetAt_of_ne (Sum.inl i0) b' hne i j
  · -- a clause block: the blocks before it are other clause blocks
    rcases b' with i' | j'
    · exfalso
      simp only [blockOf, Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hlt
      omega
    · have hne : (Sum.inr j' : Fin n ⊕ Fin m) ≠ Sum.inr j0 := by
        rintro h
        rw [Sum.inr.inj h] at hlt
        exact lt_irrefl _ hlt
      simp only [reductionMap]
      rw [map_sub, pderiv_mul, pderiv_gadgetAt_of_ne (Sum.inr j0) (Sum.inr j') hne i j,
        pderiv_target, map_sub, pderiv_one, pderiv_clausePoly]
      simp

/-- The diagonal block of a block of variables: the gadget's Jacobian matrix, times 12, in the
variables of that block. -/
theorem diag_entry (φ : Fin m → Clause n) (b : Fin n ⊕ Fin m) (i j : Fin 3) :
    jac φ (b, i) (b, j) = 12 * rename (fun j => ((b, j) : Var n m)) (jacobian ℤ i j) := by
  simp only [jac, Matrix.of_apply, jacobian]
  rcases b with i0 | j0
  · simpa [reductionMap] using pderiv_gadgetAt_self (Sum.inl i0) i j
  · simp only [reductionMap]
    rw [map_sub, pderiv_mul, pderiv_gadgetAt_self (Sum.inr j0) i j, pderiv_target, map_sub,
      pderiv_one, pderiv_clausePoly]
    simp

theorem det_block (φ : Fin m → Clause n) (b : Fin n ⊕ Fin m) :
    (Matrix.of fun i j : Fin 3 => jac φ (b, i) (b, j)).det = C (-3456) := by
  have h12 : rename (fun j => ((b, j) : Var n m)) (12 : MvPolynomial (Fin 3) ℤ) = 12 :=
    map_ofNat _ 12
  have h2 : rename (fun j => ((b, j) : Var n m)) (2 : MvPolynomial (Fin 3) ℤ) = 2 :=
    map_ofNat _ 2
  have h : (Matrix.of fun i j : Fin 3 => jac φ (b, i) (b, j))
      = (rename (fun j => ((b, j) : Var n m))).toRingHom.mapMatrix
        ((12 : MvPolynomial (Fin 3) ℤ) • jacobian ℤ) := by
    ext i j
    simp [diag_entry, h12]
  rw [h, ← RingHom.map_det, Matrix.det_smul, det_jacobian]
  simp [h12, h2]
  norm_num

/-- The determinant of the square block number `k`. -/
theorem det_toSquareBlock (φ : Fin m → Clause n) (k : Fin (m + n)) :
    ((jac φ).toSquareBlock blockOf k).det = C (-3456) := by
  -- the block of variables whose number is `k`
  obtain ⟨b, hb, hinj⟩ : ∃ b : Fin n ⊕ Fin m, (∀ c : Fin 3, blockOf ((b, c) : Var n m) = k) ∧
      ∀ a : Var n m, blockOf a = k → a.1 = b := by
    induction k using Fin.addCases with
    | left j =>
      refine ⟨Sum.inr j, fun c => rfl, ?_⟩
      rintro ⟨b', c⟩ h
      rcases b' with i' | j'
      · exfalso
        simp only [blockOf, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
        omega
      · simp only [blockOf, Fin.ext_iff, Fin.val_castAdd] at h
        exact congrArg Sum.inr (Fin.ext h)
    | right i =>
      refine ⟨Sum.inl i, fun c => rfl, ?_⟩
      rintro ⟨b', c⟩ h
      rcases b' with i' | j'
      · simp only [blockOf, Fin.ext_iff, Fin.val_natAdd] at h
        exact congrArg Sum.inl (Fin.ext (by omega))
      · exfalso
        simp only [blockOf, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
        omega
  let e : Fin 3 ≃ { a : Var n m // blockOf a = k } :=
    { toFun := fun c => ⟨(b, c), hb c⟩
      invFun := fun a => a.1.2
      left_inv := fun c => rfl
      right_inv := fun a => by
        apply Subtype.ext
        exact Prod.ext (hinj a.1 a.2).symm rfl }
  rw [← Matrix.det_submatrix_equiv_self e, ← det_block φ b]
  rfl

end KellerZero.Proofs.Keller

open KellerZero.Proofs.Keller in
theorem KellerZero.Proofs.ReductionMapIsKeller : KellerZero.Open.ReductionMapIsKeller := by
  intro n m φ
  have h := (blockTriangular φ).det_fintype
  simp only [det_toSquareBlock, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hjac : (Matrix.of fun a b => MvPolynomial.pderiv b (KellerZero.reductionMap φ a)) = jac φ := rfl
  rw [hjac, h, ← map_pow, add_comm]
