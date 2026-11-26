import KellerZero.Gadget

/-!
# The reduction as a polynomial map

`reductionMap φ` is the map of Stambler's reduction for a 3CNF formula `φ`, written as
polynomials with integer coefficients in `3 n + 3 m` variables.

* `reductionMap_eq_zero_iff`: its common zeros are the zeros in the sense of `IsZero`;
* `exists_zero_reductionMap_iff_satisfiable`: over every field of characteristic zero, the map
  has a zero exactly when `φ` is satisfiable.

That its Jacobian determinant is a nonzero constant is the open statement
`KellerZero.Open.ReductionMapIsKeller`.
-/

namespace KellerZero

open MvPolynomial

/-- The variables of the map of the reduction: three for each of the `n` variables of the
formula and three for each of its `m` clauses. -/
abbrev Var (n m : ℕ) := (Fin n ⊕ Fin m) × Fin 3

/-- Coordinate `i` of the rescaled gadget `H = 12 F + (3, 0, 0)`, in the variables of block
`b`. -/
noncomputable def gadgetAt {n m : ℕ} (b : Fin n ⊕ Fin m) (i : Fin 3) :
    MvPolynomial (Var n m) ℤ :=
  12 * rename (fun j => (b, j)) (poly ℤ i) + (![3, 0, 0] : Fin 3 → MvPolynomial (Var n m) ℤ) i

/-- The polynomial value of a literal. -/
noncomputable def literalPoly {n m : ℕ} (l : Literal n) : MvPolynomial (Var n m) ℤ :=
  if l.positive then X (Sum.inl l.var, 0) ^ 2 else 1 - X (Sum.inl l.var, 0) ^ 2

/-- The satisfaction polynomial of a clause. -/
noncomputable def clausePoly {n m : ℕ} (c : Clause n) : MvPolynomial (Var n m) ℤ :=
  1 - ∏ k, (1 - literalPoly (c k))

/-- The map of the reduction for the formula `φ`, as polynomials with integer coefficients:
the gadget on every variable block, and on clause block `j` the gadget minus
`(1 - s_j) (7, 24, 8)`. -/
noncomputable def reductionMap {n m : ℕ} (φ : Fin m → Clause n) :
    Var n m → MvPolynomial (Var n m) ℤ
  | (Sum.inl i, k) => gadgetAt (Sum.inl i) k
  | (Sum.inr j, k) => gadgetAt (Sum.inr j) k -
      (1 - clausePoly (φ j)) * (![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k

section Faithful

variable {K : Type*} [Field K] {n m : ℕ}

/-- The three coordinates of block `b` of a point. -/
def block (u : Var n m → K) (b : Fin n ⊕ Fin m) : K × K × K := (u (b, 0), u (b, 1), u (b, 2))

theorem aeval_gadgetAt (u : Var n m → K) (b : Fin n ⊕ Fin m) :
    (aeval u (gadgetAt b 0), aeval u (gadgetAt b 1), aeval u (gadgetAt b 2)) = H (block u b) := by
  simp [gadgetAt, poly, aeval_rename, H, block, P, Q, R]

theorem aeval_literalPoly (u : Var n m → K) (l : Literal n) :
    aeval u (literalPoly (m := m) l) = l.value fun i => block u (Sum.inl i) := by
  unfold literalPoly Literal.value
  split_ifs <;> simp [block]

theorem aeval_clausePoly (u : Var n m → K) (c : Clause n) :
    aeval u (clausePoly (m := m) c) = clauseValue c fun i => block u (Sum.inl i) := by
  simp [clausePoly, clauseValue, aeval_literalPoly]

/-- The definitions above say what they should: a point is a common zero of the polynomials
`reductionMap φ` exactly when its blocks form a zero in the sense of `IsZero`, the notion that
`exists_zero_iff_satisfiable` is about. -/
theorem reductionMap_eq_zero_iff (φ : Fin m → Clause n) (u : Var n m → K) :
    (∀ a, aeval u (reductionMap φ a) = 0) ↔
      IsZero φ (fun i => block u (Sum.inl i)) (fun j => block u (Sum.inr j)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [← aeval_gadgetAt]
      have h0 := h (Sum.inl i, 0)
      have h1 := h (Sum.inl i, 1)
      have h2 := h (Sum.inl i, 2)
      simp only [reductionMap] at h0 h1 h2
      rw [h0, h1, h2]
    · rw [← aeval_gadgetAt]
      have h0 := h (Sum.inr j, 0)
      have h1 := h (Sum.inr j, 1)
      have h2 := h (Sum.inr j, 2)
      simp only [reductionMap, map_sub, map_mul, map_one, aeval_clausePoly, sub_eq_zero] at h0 h1 h2
      rw [h0, h1, h2]
      simp
  · rintro ⟨hw, hv⟩ ⟨b | b, k⟩
    · have := hw b
      rw [← aeval_gadgetAt] at this
      simp only [Prod.mk.injEq] at this
      fin_cases k <;> simp [reductionMap, this]
    · have := hv b
      rw [← aeval_gadgetAt] at this
      simp only [Prod.mk.injEq] at this
      fin_cases k <;> simp [reductionMap, aeval_clausePoly, this]

end Faithful

/-- The point whose blocks are the given ones. -/
def glue {K : Type*} {n m : ℕ} (w : Fin n → K × K × K) (v : Fin m → K × K × K) : Var n m → K :=
  fun a => ![(Sum.elim w v a.1).1, (Sum.elim w v a.1).2.1, (Sum.elim w v a.1).2.2] a.2

theorem block_glue {K : Type*} {n m : ℕ} (w : Fin n → K × K × K) (v : Fin m → K × K × K)
    (b : Fin n ⊕ Fin m) : block (glue w v) b = Sum.elim w v b := by
  simp [block, glue]

/-- Stambler's reduction, for the polynomial map: over every field of characteristic zero,
`reductionMap φ` has a zero exactly when the 3CNF formula `φ` is satisfiable. -/
theorem exists_zero_reductionMap_iff_satisfiable {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (φ : Fin m → Clause n) :
    (∃ u : Var n m → K, ∀ a, aeval u (reductionMap φ a) = 0) ↔
      ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ := by
  rw [← exists_zero_iff_satisfiable (K := K) φ]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨_, _, (reductionMap_eq_zero_iff φ u).mp hu⟩
  · rintro ⟨w, v, h⟩
    refine ⟨glue w v, (reductionMap_eq_zero_iff φ (glue w v)).mpr ?_⟩
    simpa [block_glue] using h

end KellerZero
