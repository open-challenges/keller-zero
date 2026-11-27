import KellerZero.Open
import KellerZero.Certificates
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# O8: a refutation of the formula gives a refutation of its map

Substitute `X i = x_i ^ 2`, where `x_i` is the first variable of block `i`, in a Nullstellensatz
refutation of the formula. The Boolean equation becomes `x ^ 4 - x ^ 2`, which is a combination
of the three equations of the block (`quartic`). The product of a clause becomes the product
`f` of the falsity polynomials of its literals, and `f` is a combination of the equations of
the clause block and of the blocks of its variables (`fprod_eq`): the target certificate gives
`1 + (1 - f) T` in the ideal, and `f - f ^ 2` is a combination of the `x ^ 4 - x ^ 2`.

The constant is 24: every product has degree at most `2 d + 24`.
-/

namespace KellerZero.Proofs.Upper

open MvPolynomial KellerZero

variable {n m : ℕ}

/-- Substituting polynomials of degree at most `k` multiplies the degree by at most `k`. -/
theorem totalDegree_bind₁_le_mul {σ τ : Type*} (k : ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, (f i).totalDegree ≤ k) (p : MvPolynomial σ ℚ) :
    (bind₁ f p).totalDegree ≤ k * p.totalDegree := by
  have h : bind₁ f p = ∑ s ∈ p.support, bind₁ f (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [h]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have hs' : (s.sum fun _ e => e) ≤ p.totalDegree := le_totalDegree hs
  calc ∑ i ∈ s.support, (f i ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i * k := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (s i) (hf i))
    _ = (∑ i ∈ s.support, s i) * k := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * k := Nat.mul_le_mul_right k hs'
    _ = k * p.totalDegree := mul_comm _ _

/-- In a product with a nonzero factor, the other factor has no larger degree. -/
theorem totalDegree_le_of_mul {σ : Type*} (p q : MvPolynomial σ ℚ) (hq : q ≠ 0) :
    p.totalDegree ≤ (p * q).totalDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [totalDegree_mul_of_isDomain hp hq]
    exact Nat.le_add_right _ _

/-! ## The blocks -/

/-- The rescaled gadget in the variables of block `b`, with rational coefficients. -/
noncomputable def Hb (b : Fin n ⊕ Fin m) (k : Fin 3) : MvPolynomial (Var n m) ℚ :=
  12 * rename (fun c => ((b, c) : Var n m)) (poly ℚ k)
    + (![3, 0, 0] : Fin 3 → MvPolynomial (Var n m) ℚ) k

/-- The polynomial that is `1` when the literal is false: `1 - x ^ 2` or `x ^ 2`. -/
noncomputable def fal (l : Literal n) : MvPolynomial (Var n m) ℚ :=
  if l.positive then 1 - X (Sum.inl l.var, 0) ^ 2 else X (Sum.inl l.var, 0) ^ 2

/-- The product of the falsity polynomials of a clause. -/
noncomputable def fprod (c : Clause n) : MvPolynomial (Var n m) ℚ := ∏ l, fal (c l)

theorem kx_inl (φ : Fin m → Clause n) (i : Fin n) (k : Fin 3) :
    kellerAxioms φ (Sum.inl i, k) = Hb (Sum.inl i) k := by
  simp [kellerAxioms, reductionMap, map_gadgetAt, Hb]

theorem map_one_sub_literalPoly (l : Literal n) :
    map (Int.castRingHom ℚ) (1 - literalPoly (m := m) l) = fal l := by
  unfold literalPoly fal
  split_ifs <;> simp

theorem kx_inr (φ : Fin m → Clause n) (j : Fin m) (k : Fin 3) :
    kellerAxioms φ (Sum.inr j, k)
      = Hb (Sum.inr j) k - fprod (φ j) * (![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℚ) k := by
  have hc : map (Int.castRingHom ℚ) (1 - clausePoly (m := m) (φ j)) = fprod (φ j) := by
    have : (1 : MvPolynomial (Var n m) ℤ) - clausePoly (φ j) = ∏ l, (1 - literalPoly (φ j l)) := by
      simp [clausePoly]
    rw [this, map_prod]
    exact Finset.prod_congr rfl fun l _ => map_one_sub_literalPoly (φ j l)
  have h7 : map (Int.castRingHom ℚ) ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k)
      = (![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℚ) k := by
    fin_cases k <;> simp [map_ofNat]
  have hrm : kellerAxioms φ (Sum.inr j, k)
      = map (Int.castRingHom ℚ) (gadgetAt (Sum.inr j) k)
        - map (Int.castRingHom ℚ) (1 - clausePoly (φ j))
          * map (Int.castRingHom ℚ) ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k) := by
    simp only [kellerAxioms, reductionMap]
    rw [map_sub, map_mul]
  rw [hrm, hc, h7, map_gadgetAt, Hb]

/-- The multipliers of `quartic_certificate`, divided by 24, in the variables of block `b`. -/
noncomputable def bq (b : Fin n ⊕ Fin m) : Fin 3 → MvPolynomial (Var n m) ℚ :=
  ![C (1 / 24) * (8 * X (b, 0) ^ 4),
    C (1 / 24) * (-2 * X (b, 0) ^ 4 * X (b, 1) - 3 * X (b, 0) ^ 3),
    C (1 / 24) * (2 * X (b, 0) ^ 4 * X (b, 1) ^ 3 + 3 * X (b, 0) ^ 3 * X (b, 1) ^ 2 - X (b, 0))]

/-- The multipliers of `target_certificate`, divided by 24, in the variables of block `b`. -/
noncomputable def gt (b : Fin n ⊕ Fin m) : Fin 3 → MvPolynomial (Var n m) ℚ :=
  ![C (1 / 24) * (6 * X (b, 0) ^ 2 * X (b, 1) - 6 * X (b, 0) ^ 2 + 6 * X (b, 0)),
    C (1 / 24) * (-2 * X (b, 0) ^ 2 * X (b, 1) ^ 2 + X (b, 0) ^ 2 * X (b, 1) + X (b, 0) ^ 2
      - 4 * X (b, 0) * X (b, 1) + 2 * X (b, 0) - 2),
    C (1 / 24) * (-3 * X (b, 0) ^ 2 * X (b, 1) ^ 3 + 3 * X (b, 0) ^ 2 * X (b, 1) ^ 2
      - 6 * X (b, 0) * X (b, 1) ^ 2 + 6 * X (b, 0) * X (b, 1) - 3 * X (b, 1) + 3)]

/-- `x ^ 4 - x ^ 2` is a combination of the three equations of a block. -/
theorem quartic (b : Fin n ⊕ Fin m) :
    ∑ k, bq b k * Hb b k = X (b, 0) ^ 4 - X (b, 0) ^ 2 := by
  apply MvPolynomial.funext
  intro v
  simp [Fin.sum_univ_three, bq, Hb, poly, map_ofNat]
  ring

/-- `1` is a combination of the three equations `H = (7, 24, 8)` of a block. -/
theorem target (b : Fin n ⊕ Fin m) :
    ∑ k, gt b k * (Hb b k - (![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℚ) k) = 1 := by
  apply MvPolynomial.funext
  intro v
  simp [Fin.sum_univ_three, gt, Hb, poly, map_ofNat]
  ring

/-- What multiplies `1 - f` in the combination of the equations of a clause block. -/
noncomputable def tau (b : Fin n ⊕ Fin m) : MvPolynomial (Var n m) ℚ :=
  ∑ k, gt b k * (![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℚ) k

theorem fal_sq (l : Literal n) :
    (fal (m := m) l) ^ 2 - fal l = X (Sum.inl l.var, 0) ^ 4 - X (Sum.inl l.var, 0) ^ 2 := by
  unfold fal
  split_ifs <;> ring

/-- The cofactor of `fal (c l) ^ 2 - fal (c l)` in `f ^ 2 - f`. -/
noncomputable def cof (c : Clause n) : Fin 3 → MvPolynomial (Var n m) ℚ :=
  ![fal (c 1) ^ 2 * fal (c 2) ^ 2, fal (c 0) * fal (c 2) ^ 2, fal (c 0) * fal (c 1)]

/-- The product of a clause is a combination of the equations of its clause block and of
`x ^ 4 - x ^ 2` for its three variables. -/
theorem fprod_eq (φ : Fin m → Clause n) (j : Fin m) :
    fprod (φ j) = ∑ k, (fprod (φ j) * gt (Sum.inr j) k) * kellerAxioms φ (Sum.inr j, k)
      + tau (Sum.inr j) * ∑ l, cof (φ j) l
        * (X (Sum.inl (φ j l).var, 0) ^ 4 - X (Sum.inl (φ j l).var, 0) ^ 2) := by
  have ht := target (n := n) (m := m) (Sum.inr j)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at ht
  simp only [Fin.sum_univ_three, kx_inr, tau, cof, ← fal_sq, fprod, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (-(fal (φ j 0) * fal (φ j 1) * fal (φ j 2)) : MvPolynomial (Var n m) ℚ) * ht

/-! ## Degrees -/

theorem deg_poly0 : (poly ℚ 0).totalDegree ≤ 7 := by
  simp only [poly, Matrix.cons_val_zero]
  exact le_trans (by td) (by norm_num)

theorem deg_poly1 : (poly ℚ 1).totalDegree ≤ 6 := by
  simp only [poly, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact le_trans (by td) (by norm_num)

theorem deg_poly2 : (poly ℚ 2).totalDegree ≤ 4 := by
  simp only [poly, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact le_trans (by td) (by norm_num)

theorem deg_fal (l : Literal n) : (fal (m := m) l).totalDegree ≤ 2 := by
  unfold fal
  split_ifs <;> exact le_trans (by td) (by norm_num)

theorem deg_fprod (c : Clause n) : (fprod (m := m) c).totalDegree ≤ 6 := by
  have h0 := deg_fal (m := m) (c 0)
  have h1 := deg_fal (m := m) (c 1)
  have h2 := deg_fal (m := m) (c 2)
  simp only [fprod, Fin.prod_univ_three]
  exact le_trans (by td) (by norm_num)

theorem deg_cof (c : Clause n) (l : Fin 3) : (cof (m := m) c l).totalDegree ≤ 8 := by
  have h0 := deg_fal (m := m) (c 0)
  have h1 := deg_fal (m := m) (c 1)
  have h2 := deg_fal (m := m) (c 2)
  fin_cases l <;> simp only [cof, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    exact le_trans (by td) (by norm_num)

theorem deg_tau (b : Fin n ⊕ Fin m) : (tau b).totalDegree ≤ 5 := by
  simp only [tau, gt, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact le_trans (by td) (by norm_num)

/-- A multiplier of `quartic` times its equation has degree at most 11. -/
theorem deg_bq_mul (b : Fin n ⊕ Fin m) (k : Fin 3) : (bq b k * Hb b k).totalDegree ≤ 11 := by
  have h0 := deg_poly0
  have h1 := deg_poly1
  have h2 := deg_poly2
  fin_cases k <;> simp only [bq, Hb, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> exact le_trans (by td) (by norm_num)

/-- A multiplier of `target` times the equation of a clause block has degree at most 11. -/
theorem deg_gt_mul (φ : Fin m → Clause n) (j : Fin m) (k : Fin 3) :
    (gt (Sum.inr j) k * kellerAxioms φ (Sum.inr j, k)).totalDegree ≤ 11 := by
  have h0 := deg_poly0
  have h1 := deg_poly1
  have h2 := deg_poly2
  have hf := deg_fprod (m := m) (φ j)
  rw [kx_inr]
  fin_cases k <;> simp only [gt, Hb, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> exact le_trans (by td) (by norm_num)

/-! ## The substitution -/

/-- `X i` goes to the square of the first variable of block `i`. -/
noncomputable def sqv (i : Fin n) : MvPolynomial (Var n m) ℚ := X (Sum.inl i, 0) ^ 2

theorem deg_sq (i : Fin n) : (sqv (m := m) i).totalDegree ≤ 2 := by
  unfold sqv
  exact le_trans (by td) (by norm_num)

theorem bind₁_literalAxiom (l : Literal n) : bind₁ (sqv (m := m)) (literalAxiom l) = fal l := by
  unfold literalAxiom fal sqv
  split_ifs <;> simp

theorem formulaAxioms_ne_zero (φ : Fin m → Clause n) (a : Fin n ⊕ Fin m) :
    formulaAxioms φ a ≠ 0 := by
  intro h
  have h2 := congrArg (eval fun _ => (2 : ℚ)) h
  rcases a with i | j
  · simp [formulaAxioms] at h2
    norm_num at h2
  · simp only [formulaAxioms, map_prod, map_zero, Finset.prod_eq_zero_iff, Finset.mem_univ,
      true_and] at h2
    obtain ⟨l, hl⟩ := h2
    unfold literalAxiom at hl
    split_ifs at hl
    · norm_num at hl
    · simp at hl

/-- The substituted multiplier of an equation of the formula has degree at most `2 d`. -/
theorem deg_hat (φ : Fin m → Clause n) (g : Fin n ⊕ Fin m → MvPolynomial (Fin n) ℚ) (d : ℕ)
    (hd : ∀ a, (g a * formulaAxioms φ a).totalDegree ≤ d) (a : Fin n ⊕ Fin m) :
    (bind₁ (sqv (m := m)) (g a)).totalDegree ≤ 2 * d :=
  (totalDegree_bind₁_le_mul 2 sqv deg_sq (g a)).trans
    (Nat.mul_le_mul_left 2 ((totalDegree_le_of_mul _ _ (formulaAxioms_ne_zero φ a)).trans (hd a)))

end KellerZero.Proofs.Upper

open KellerZero.Proofs.Upper MvPolynomial KellerZero in
theorem KellerZero.Proofs.RefutationOfMap : KellerZero.Open.RefutationOfMap := by
  refine ⟨24, fun n m φ d h => ?_⟩
  obtain ⟨g, hg, hd⟩ := h
  -- the substituted multipliers
  set gh : Fin n ⊕ Fin m → MvPolynomial (Var n m) ℚ := fun a => bind₁ sqv (g a) with hgh
  have hgh_deg : ∀ a, (gh a).totalDegree ≤ 2 * d := deg_hat φ g d hd
  -- what multiplies `x_i ^ 4 - x_i ^ 2`
  set W : Fin n → MvPolynomial (Var n m) ℚ := fun i =>
    gh (Sum.inl i) + ∑ j, ∑ l, if (φ j l).var = i
      then gh (Sum.inr j) * tau (Sum.inr j) * cof (φ j) l else 0 with hW
  refine ⟨fun a => match a with
    | (Sum.inl i, k) => W i * bq (Sum.inl i) k
    | (Sum.inr j, k) => gh (Sum.inr j) * fprod (φ j) * gt (Sum.inr j) k, ?_, ?_⟩
  · -- the combination is 1
    have h1 : bind₁ (sqv (m := m)) (∑ a, g a * formulaAxioms φ a) = 1 := by rw [hg, map_one]
    rw [Fintype.sum_sum_type, map_add, map_sum, map_sum] at h1
    have hB : ∀ i : Fin n, bind₁ (sqv (m := m)) (g (Sum.inl i) * formulaAxioms φ (Sum.inl i))
        = gh (Sum.inl i) * (X (Sum.inl i, 0) ^ 4 - X (Sum.inl i, 0) ^ 2) := by
      intro i
      simp only [formulaAxioms, map_mul, map_sub, map_pow, bind₁_X_right, hgh, sqv]
      ring
    have hA : ∀ j : Fin m, bind₁ (sqv (m := m)) (g (Sum.inr j) * formulaAxioms φ (Sum.inr j))
        = gh (Sum.inr j) * fprod (φ j) := by
      intro j
      simp only [formulaAxioms, map_mul, map_prod, bind₁_literalAxiom, hgh, fprod]
    simp only [hB, hA] at h1
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    have hL : ∀ i : Fin n, ∑ k, (W i * bq (Sum.inl i) k) * kellerAxioms φ (Sum.inl i, k)
        = W i * (X (Sum.inl i, 0) ^ 4 - X (Sum.inl i, 0) ^ 2) := by
      intro i
      rw [← quartic (Sum.inl i), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [kx_inl]; ring
    have hR : ∀ j : Fin m, ∑ k, (gh (Sum.inr j) * fprod (φ j) * gt (Sum.inr j) k)
          * kellerAxioms φ (Sum.inr j, k)
        = gh (Sum.inr j) * ∑ k, (fprod (φ j) * gt (Sum.inr j) k) * kellerAxioms φ (Sum.inr j, k) := by
      intro j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hL, hR]
    -- the part of `W` that comes from the clauses
    have hsw : ∑ i : Fin n, (∑ j, ∑ l, if (φ j l).var = i
          then gh (Sum.inr j) * tau (Sum.inr j) * cof (φ j) l else 0)
          * (X (Sum.inl i, 0) ^ 4 - X (Sum.inl i, 0) ^ 2)
        = ∑ j, gh (Sum.inr j) * (tau (Sum.inr j) * ∑ l, cof (φ j) l
          * (X (Sum.inl (φ j l).var, 0) ^ 4 - X (Sum.inl (φ j l).var, 0) ^ 2)) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
      ring
    have hWsum : ∑ i : Fin n, W i * (X (Sum.inl i, 0) ^ 4 - X (Sum.inl i, 0) ^ 2)
        = ∑ i : Fin n, gh (Sum.inl i) * (X (Sum.inl i, 0) ^ 4 - X (Sum.inl i, 0) ^ 2)
          + ∑ j, gh (Sum.inr j) * (tau (Sum.inr j) * ∑ l, cof (φ j) l
            * (X (Sum.inl (φ j l).var, 0) ^ 4 - X (Sum.inl (φ j l).var, 0) ^ 2)) := by
      rw [← hsw, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hW]; ring
    rw [hWsum, add_assoc, ← Finset.sum_add_distrib, ← h1]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, add_comm, ← fprod_eq φ j]
  · -- the degrees
    rintro ⟨i | j, k⟩
    · have hWdeg : (W i).totalDegree ≤ 2 * d + 13 := by
        rw [hW]
        refine (totalDegree_add _ _).trans (max_le ((hgh_deg _).trans (by omega)) ?_)
        refine totalDegree_finsetSum_le fun j _ => totalDegree_finsetSum_le fun l _ => ?_
        split_ifs
        · have h1 := hgh_deg (Sum.inr j)
          have h2 := deg_tau (n := n) (m := m) (Sum.inr j)
          have h3 := deg_cof (m := m) (φ j) l
          exact le_trans (Deg.mul (Deg.mul h1 h2) h3) (by omega)
        · simp
      show (W i * bq (Sum.inl i) k * kellerAxioms φ (Sum.inl i, k)).totalDegree ≤ 2 * d + 24
      rw [kx_inl, mul_assoc]
      exact le_trans (Deg.mul hWdeg (deg_bq_mul (Sum.inl i) k)) (by omega)
    · show (gh (Sum.inr j) * fprod (φ j) * gt (Sum.inr j) k
        * kellerAxioms φ (Sum.inr j, k)).totalDegree ≤ 2 * d + 24
      rw [mul_assoc]
      have h1 := hgh_deg (Sum.inr j)
      have h2 := deg_fprod (m := m) (φ j)
      exact le_trans (Deg.mul (Deg.mul h1 h2) (deg_gt_mul φ j k)) (by omega)
