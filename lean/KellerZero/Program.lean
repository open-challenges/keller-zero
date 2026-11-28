import KellerZero.Cubic10
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# A map with constant Jacobian determinant can carry a computation for free

The map of the reduction needs a copy of the gadget wherever something is *chosen* (one per
variable of the formula) and one more where the result is *checked*. Everything in between is a
computation, and a computation costs no gadget: a new variable `c` with the coordinate
`c - (a polynomial in the variables before it)` contributes a `1` to the diagonal of a
triangular block of the Jacobian matrix.

This file has the general statements:

* `det_jacobian_sum`: the Jacobian determinant of a map whose first group of coordinates
  involves only the first group of variables is the product of the two diagonal blocks;
* `det_of_rank_unitriangular`: a matrix that is triangular for some ranking of its index, with
  ones on the diagonal, has determinant one;
* `det_scaled`: the gadget of degree three with its three main coordinates multiplied by
  `12 ρ` has Jacobian determinant `ρ ^ 3 * (-3456)`;
* `det_programMap`: `n` gadgets, any triangular computation on top of them, and one more gadget
  that reads the result: Jacobian determinant `(-3456) ^ n * (ρ ^ 3 * (-3456))`.
-/

namespace KellerZero

open MvPolynomial

section General

variable {R : Type*} [CommRing R]

/-- A triangular matrix with ones on the diagonal has determinant one. Triangular means: for
some ranking of the index, entry `(c, d)` vanishes unless `c = d` or `d` has smaller rank. -/
theorem det_of_rank_unitriangular {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ R)
    (rank : κ → ℕ) (h1 : ∀ c, M c c = 1) (h2 : ∀ c d, c ≠ d → rank c ≤ rank d → M c d = 0) :
    M.det = 1 := by
  have hT : M.BlockTriangular (OrderDual.toDual ∘ rank) := by
    intro c d hcd
    have hlt : rank c < rank d := hcd
    exact h2 c d (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt) hlt.le
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock (OrderDual.toDual ∘ rank) a = 1 := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨c, hc⟩ := i
    obtain ⟨d, hd⟩ := j
    rw [Matrix.one_apply]
    change M c d = _
    by_cases hcd : c = d
    · subst hcd
      simp [h1]
    · have hr : rank c ≤ rank d := by
        have : OrderDual.toDual (rank c) = OrderDual.toDual (rank d) := hc.trans hd.symm
        exact (OrderDual.toDual.injective this).le
      simp [h2 c d hcd hr, hcd]
  rw [this, Matrix.det_one]

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- If the first group of coordinates involves only the first group of variables, the Jacobian
determinant is the product of the determinants of the two diagonal blocks. -/
theorem det_jacobian_sum (A : α → MvPolynomial α R) (B : β → MvPolynomial (α ⊕ β) R) :
    (Matrix.of fun a b => pderiv b (Sum.elim (fun i => rename Sum.inl (A i)) B a)).det
      = rename Sum.inl (Matrix.of fun i j => pderiv j (A i)).det
        * (Matrix.of fun b b' => pderiv (Sum.inr b') (B b)).det := by
  set JA : Matrix α α (MvPolynomial (α ⊕ β) R) :=
    Matrix.of fun i k => rename Sum.inl (pderiv k (A i)) with hJA
  set Cb : Matrix β α (MvPolynomial (α ⊕ β) R) :=
    Matrix.of fun b k => pderiv (Sum.inl k) (B b) with hC
  set D : Matrix β β (MvPolynomial (α ⊕ β) R) :=
    Matrix.of fun b b' => pderiv (Sum.inr b') (B b) with hD
  have hM : (Matrix.of fun a b => pderiv b (Sum.elim (fun i => rename Sum.inl (A i)) B a))
      = Matrix.fromBlocks JA 0 Cb D := by
    ext (i | b) (k | c)
    · simp [hJA, pderiv_rename Sum.inl_injective]
    · simp [pderiv_inr_rename_inl]
    · simp [hC]
    · simp [hD]
  have hJA1 : JA.det = rename Sum.inl (Matrix.of fun i j => pderiv j (A i)).det := by
    have : JA = (rename (R := R) (Sum.inl : α → α ⊕ β)).toRingHom.mapMatrix
        (Matrix.of fun i j => pderiv j (A i)) := by
      ext i k
      simp [hJA]
    rw [this, ← RingHom.map_det]
    rfl
  rw [hM, Matrix.det_fromBlocks_zero₁₂, hJA1]

end General

section Scaled

/-- The constant terms of the rescaled gadget. -/
noncomputable def shift3 : Fin 3 → MvPolynomial V10 ℤ := ![3, 0, 0]

/-- The gadget of degree three with its three main coordinates rescaled: `ρ (12 F + (3, 0, 0))`
followed by the seven wires. With `ρ = 1` this is the block of a variable. -/
noncomputable def scaled (ρ : ℤ) : V10 → MvPolynomial V10 ℤ :=
  Sum.elim (fun k => C ρ * (12 * cubic10 k + shift3 k)) wire10

theorem pderiv_shift3 (b : V10) (k : Fin 3) : pderiv b (shift3 k) = 0 := by
  fin_cases k <;> simp [shift3, pderiv_ofNat]

/-- The Jacobian determinant of the rescaled gadget. -/
theorem det_scaled (ρ : ℤ) :
    (Matrix.of fun a b => pderiv b (scaled ρ a)).det = C (ρ ^ 3 * (-3456)) := by
  have hmul : (Matrix.of fun a b => pderiv b (scaled ρ a))
      = Matrix.diagonal (Sum.elim (fun _ : Fin 3 => (C (12 * ρ) : MvPolynomial V10 ℤ))
          (fun _ : Fin 7 => 1))
        * (Matrix.of fun a b => pderiv b (cubic10Map a)) := by
    refine Matrix.ext fun a b => ?_
    rcases a with k | w
    · rw [Matrix.diagonal_mul]
      simp only [Matrix.of_apply, scaled, Sum.elim_inl, cubic10Map_inl, pderiv_C, map_add,
        pderiv_mul, pderiv_ofNat, pderiv_shift3, map_mul, map_ofNat]
      ring
    · rw [Matrix.diagonal_mul]
      simp [scaled, cubic10Map_inr]
  rw [hmul, Matrix.det_mul, Matrix.det_diagonal, det_cubic10Map, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_pow, mul_one]
  rw [← map_pow, ← map_mul]
  congr 1
  ring

theorem totalDegree_scaled (ρ : ℤ) (a : V10) : (scaled ρ a).totalDegree ≤ 3 := by
  rcases a with k | w
  · have h := totalDegree_cubic10 k
    have h3 : (shift3 k).totalDegree ≤ 0 := Deg.vec300 k
    simp only [scaled, Sum.elim_inl]
    exact le_trans (by td) (by norm_num)
  · exact totalDegree_wire10 w

end Scaled

section ProgramMap

variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The variables of the gadgets of the formula's variables, and of the computation. -/
abbrev Inner (n : ℕ) (κ : Type*) := Fin n × V10 ⊕ κ

/-- All the variables: those of `Inner`, and the ten of the gadget that checks the result. -/
abbrev PVar (n : ℕ) (κ : Type*) := Inner n κ ⊕ V10

/-- `n` copies of the gadget of degree three, each in its own ten variables. -/
noncomputable def blocksMap (n : ℕ) : Fin n × V10 → MvPolynomial (Fin n × V10) ℤ :=
  fun ia => rename (fun a => (ia.1, a)) (scaled 1 ia.2)

/-- The gadgets and a computation on top of them: the computation variable `c` has the
coordinate `c - prog c`. -/
noncomputable def innerMap (prog : κ → MvPolynomial (Inner n κ) ℤ) :
    Inner n κ → MvPolynomial (Inner n κ) ℤ :=
  Sum.elim (fun ia => rename Sum.inl (blocksMap n ia)) (fun c => X (Sum.inr c) - prog c)

/-- The target that the gadget never takes. -/
def target : Fin 3 → ℤ := ![7, 24, 8]

/-- The gadget that checks the result `out` of the computation: its three main coordinates are
`ρ H(v) - (ρ - out) (7, 24, 8)`. -/
noncomputable def checker (ρ : ℤ) (out : MvPolynomial (Inner n κ) ℤ) :
    V10 → MvPolynomial (PVar n κ) ℤ :=
  Sum.elim
    (fun k => rename Sum.inr (scaled ρ (Sum.inl k)) - C (target k) * (C ρ - rename Sum.inl out))
    (fun w => rename Sum.inr (scaled ρ (Sum.inr w)))

/-- The whole map: `n` gadgets, a computation, and a gadget that checks its result. -/
noncomputable def programMap (prog : κ → MvPolynomial (Inner n κ) ℤ) (ρ : ℤ)
    (out : MvPolynomial (Inner n κ) ℤ) : PVar n κ → MvPolynomial (PVar n κ) ℤ :=
  Sum.elim (fun a => rename Sum.inl (innerMap prog a)) (checker ρ out)

omit [Fintype κ] [DecidableEq κ] in
theorem det_blocksMap (n : ℕ) :
    (Matrix.of fun a b => pderiv b (blocksMap n a)).det = C ((-3456) ^ n) := by
  classical
  set M : Fin n → Matrix V10 V10 (MvPolynomial (Fin n × V10) ℤ) := fun i =>
    (rename (R := ℤ) (fun a : V10 => ((i, a) : Fin n × V10))).toRingHom.mapMatrix
      (Matrix.of fun a b => pderiv b (scaled 1 a)) with hMdef
  have hsub : (Matrix.of fun a b => pderiv b (blocksMap n a))
      = (Matrix.blockDiagonal M).submatrix (Equiv.prodComm (Fin n) V10)
          (Equiv.prodComm (Fin n) V10) := by
    refine Matrix.ext fun ia jb => ?_
    obtain ⟨i, a⟩ := ia
    obtain ⟨j, b⟩ := jb
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.blockDiagonal_apply, blocksMap]
    by_cases hij : i = j
    · subst hij
      have hinj : Function.Injective (fun a : V10 => ((i, a) : Fin n × V10)) :=
        fun _ _ h => (Prod.mk.inj h).2
      have h := pderiv_rename (R := ℤ) hinj b (scaled 1 a)
      simp only [↓reduceIte, hMdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact h
    · simp only [hij, ↓reduceIte]
      apply pderiv_eq_zero_of_notMem_vars
      intro hmem
      have := (vars_rename _ _) hmem
      simp only [Finset.mem_image] at this
      obtain ⟨c, -, hc⟩ := this
      exact hij (Prod.mk.inj hc).1
  rw [hsub, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  have hM : ∀ i, (M i).det = C (-3456) := by
    intro i
    rw [hMdef]
    simp only
    rw [← RingHom.map_det, det_scaled]
    change rename _ (C ((1 : ℤ) ^ 3 * (-3456))) = C (-3456)
    rw [rename_C]
    norm_num
  simp [hM]

/-- The Jacobian determinant of `n` gadgets, a triangular computation and a checking gadget. -/
theorem det_programMap (prog : κ → MvPolynomial (Inner n κ) ℤ) (ρ : ℤ)
    (out : MvPolynomial (Inner n κ) ℤ) (rank : κ → ℕ)
    (hprog : ∀ c d, rank c ≤ rank d → pderiv (Sum.inr d) (prog c) = 0) :
    (Matrix.of fun a b => pderiv b (programMap prog ρ out a)).det
      = C ((-3456) ^ n * (ρ ^ 3 * (-3456))) := by
  have hinner : (Matrix.of fun a b => pderiv b (innerMap prog a)).det = C ((-3456) ^ n) := by
    rw [innerMap, det_jacobian_sum, det_blocksMap, rename_C]
    rw [det_of_rank_unitriangular _ rank]
    · rw [mul_one]
    · intro c
      simp [hprog c c le_rfl]
    · intro c d hcd hr
      simp [hprog c d hr, Ne.symm hcd]
  have hD : (Matrix.of fun b b' : V10 => pderiv (Sum.inr b') (checker (n := n) ρ out b))
      = (rename (R := ℤ) (Sum.inr : V10 → PVar n κ)).toRingHom.mapMatrix
        (Matrix.of fun a b => pderiv b (scaled ρ a)) := by
    refine Matrix.ext fun b b' => ?_
    have h := pderiv_rename (R := ℤ) (Sum.inr_injective (α := Inner n κ)) b' (scaled ρ b)
    rcases b with k | w
    · simp only [Matrix.of_apply, checker, Sum.elim_inl, map_sub, pderiv_mul, pderiv_C,
        pderiv_inr_rename_inl, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [h]
      simp
    · simp only [Matrix.of_apply, checker, Sum.elim_inr, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact h
  rw [programMap, det_jacobian_sum, hinner, hD, ← RingHom.map_det, det_scaled]
  change rename _ (C _) * rename _ (C _) = _
  rw [rename_C, rename_C, ← map_mul]

omit [Fintype κ] [DecidableEq κ] in
/-- Every coordinate has degree at most three if the computation does. -/
theorem totalDegree_programMap (prog : κ → MvPolynomial (Inner n κ) ℤ) (ρ : ℤ)
    (out : MvPolynomial (Inner n κ) ℤ) (hprog : ∀ c, (prog c).totalDegree ≤ 3)
    (hout : out.totalDegree ≤ 3) (a : PVar n κ) : (programMap prog ρ out a).totalDegree ≤ 3 := by
  rcases a with (⟨i, a⟩ | c) | (k | w)
  · simp only [programMap, innerMap, blocksMap, Sum.elim_inl]
    exact Deg.rename _ (Deg.rename _ (Deg.rename _ (totalDegree_scaled 1 a)))
  · have h := hprog c
    simp only [programMap, innerMap, Sum.elim_inl, Sum.elim_inr]
    refine Deg.rename _ ?_
    exact le_trans (by td) (by norm_num)
  · have h := totalDegree_scaled ρ (Sum.inl k)
    simp only [programMap, checker, Sum.elim_inl, Sum.elim_inr]
    exact le_trans (Deg.sub (Deg.rename _ h)
      (Deg.mul (Deg.const _) (Deg.sub (Deg.const _) (Deg.rename _ hout)))) (by norm_num)
  · exact Deg.rename _ (totalDegree_scaled ρ (Sum.inr w))

end ProgramMap

section Zeros

variable {K : Type*} [Field K] {n : ℕ} {κ : Type*}

/-- The three main coordinates of the rescaled gadget `H = 12 F + (3, 0, 0)`, as functions. -/
def Hc (k : Fin 3) (x y z : K) : K := ![12 * P x y z + 3, 12 * Q x y z, 12 * R x y z] k

theorem Hc_eq (x y z : K) : (Hc 0 x y z, Hc 1 x y z, Hc 2 x y z) = H (x, y, z) := by
  simp [Hc, H]

/-- At a point of a block where the seven wires vanish, the three main coordinates take the
values of the gadget. -/
theorem aeval_scaled_inl (ρ : ℤ) (u : V10 → K) (hw : ∀ w, aeval u (wire10 w) = 0) (k : Fin 3) :
    aeval u (scaled ρ (Sum.inl k))
      = (ρ : K) * Hc k (u (Sum.inl 0)) (u (Sum.inl 1)) (u (Sum.inl 2)) := by
  have hc : aeval u (cubic10 k) = aeval (fun j => u (Sum.inl j)) (poly ℤ k) := by
    rw [← cubic10_eq k, map_sub, aeval_rename, aeval_bind₁]
    have h0 : (fun c => aeval u (wire10 c)) = (0 : Fin 7 → K) := funext hw
    rw [h0, aeval_zero, constantCoeff_carry10, map_zero, sub_zero]
    rfl
  simp only [scaled, Sum.elim_inl, map_mul, map_add, hc, aeval_C]
  fin_cases k <;> simp [poly, shift3, Hc, P, Q, R]

/-- At a point of a block where the wires vanish, the wire `h` holds the square of `x`. -/
theorem wire_h_eq (u : V10 → K) (hw : ∀ w, aeval u (wire10 w) = 0) :
    u (Sum.inr 3) = u (Sum.inl 0) ^ 2 := by
  have h := hw 3
  simp [wire10] at h
  linear_combination h

/-- A point is a zero of the whole map exactly when every block of a variable is a zero of the
gadget, every computation variable holds the value of its polynomial, and the checking gadget
takes the value `(ρ - out) (7, 24, 8) / ρ`. -/
theorem programMap_eq_zero_iff (prog : κ → MvPolynomial (Inner n κ) ℤ) (ρ : ℤ)
    (out : MvPolynomial (Inner n κ) ℤ) (v : PVar n κ → K) :
    (∀ a, aeval v (programMap prog ρ out a) = 0) ↔
      (∀ i a, aeval (fun b => v (Sum.inl (Sum.inl (i, b)))) (scaled 1 a) = 0) ∧
      (∀ c, v (Sum.inl (Sum.inr c)) = aeval (fun a => v (Sum.inl a)) (prog c)) ∧
      (∀ k, aeval (fun b => v (Sum.inr b)) (scaled ρ (Sum.inl k))
        = (target k : K) * ((ρ : K) - aeval (fun a => v (Sum.inl a)) out)) ∧
      (∀ w, aeval (fun b => v (Sum.inr b)) (wire10 w) = 0) := by
  constructor
  · intro h
    refine ⟨fun i a => ?_, fun c => ?_, fun k => ?_, fun w => ?_⟩
    · have := h (Sum.inl (Sum.inl (i, a)))
      simpa [programMap, innerMap, blocksMap, aeval_rename, Function.comp_def] using this
    · have := h (Sum.inl (Sum.inr c))
      simp only [programMap, innerMap, Sum.elim_inl, Sum.elim_inr, aeval_rename, map_sub,
        aeval_X, Function.comp_def, sub_eq_zero] at this
      exact this
    · have := h (Sum.inr (Sum.inl k))
      simp only [programMap, checker, Sum.elim_inl, Sum.elim_inr, aeval_rename, map_sub, map_mul,
        aeval_C, Function.comp_def, sub_eq_zero] at this
      simpa using this
    · have := h (Sum.inr (Sum.inr w))
      simpa [programMap, checker, scaled, aeval_rename, Function.comp_def] using this
  · rintro ⟨h1, h2, h3, h4⟩ ((⟨i, a⟩ | c) | (k | w))
    · simpa [programMap, innerMap, blocksMap, aeval_rename, Function.comp_def] using h1 i a
    · simp only [programMap, innerMap, Sum.elim_inl, Sum.elim_inr, aeval_rename, map_sub,
        aeval_X, Function.comp_def, sub_eq_zero]
      exact h2 c
    · simp only [programMap, checker, Sum.elim_inl, Sum.elim_inr, aeval_rename, map_sub, map_mul,
        aeval_C, Function.comp_def, sub_eq_zero]
      simpa using h3 k
    · simpa [programMap, checker, scaled, aeval_rename, Function.comp_def] using h4 w

/-- A block is a zero of the gadget exactly when its wires vanish and its point is a zero of
`H`. -/
theorem scaled_one_eq_zero_iff (u : V10 → K) :
    (∀ a, aeval u (scaled 1 a) = 0) ↔
      (∀ w, aeval u (wire10 w) = 0) ∧
        H (u (Sum.inl 0), u (Sum.inl 1), u (Sum.inl 2)) = (0, 0, 0) := by
  constructor
  · intro h
    have hw : ∀ w, aeval u (wire10 w) = 0 := fun w => by simpa [scaled] using h (Sum.inr w)
    refine ⟨hw, ?_⟩
    rw [← Hc_eq]
    have h0 := h (Sum.inl 0)
    have h1 := h (Sum.inl 1)
    have h2 := h (Sum.inl 2)
    rw [aeval_scaled_inl 1 u hw] at h0 h1 h2
    simp only [Int.cast_one, one_mul] at h0 h1 h2
    rw [h0, h1, h2]
  · rintro ⟨hw, hH⟩ (k | w)
    · rw [aeval_scaled_inl 1 u hw, Int.cast_one, one_mul]
      rw [← Hc_eq] at hH
      simp only [Prod.mk.injEq] at hH
      fin_cases k
      · exact hH.1
      · exact hH.2.1
      · exact hH.2.2
    · simpa [scaled] using hw w

end Zeros

end KellerZero
