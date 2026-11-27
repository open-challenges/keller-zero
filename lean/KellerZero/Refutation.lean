import KellerZero.Reduction
import KellerZero.Degree
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Refuting the map is as hard as refuting the formula

A *Nullstellensatz refutation of degree `d`* of a system of polynomial equations `a i = 0` is a
combination `∑ g i * a i = 1` in which every product `g i * a i` has degree at most `d`.

`refutation_of_formula`: for every 3CNF formula `φ`, a Nullstellensatz refutation of degree `d`
of the equations "the map of the reduction is zero" gives a Nullstellensatz refutation of degree
at most `d` of the usual equations of `φ` (the Boolean equations `X i ^ 2 - X i = 0` and one
product of literals for every clause).

So every lower bound on the degree of refutations of formulas is a lower bound on the degree
of certificates that a map with constant Jacobian determinant has no zero. The proof substitutes
a point for every block: the line through the two points `(0, 0, -1/4)` and `(1, -3/2, 13/2)`
for a variable block, the point `(0, 0, -1/4)` for a clause block. The substitution has degree
one, so it does not raise degrees, and it sends every equation of the map to a multiple of one
equation of the formula.
-/

namespace KellerZero

open MvPolynomial

/-- A Nullstellensatz refutation of degree at most `d` of the system `a i = 0`. -/
def NSRefutation {ι σ : Type*} [Fintype ι] (a : ι → MvPolynomial σ ℚ) (d : ℕ) : Prop :=
  ∃ g : ι → MvPolynomial σ ℚ, ∑ i, g i * a i = 1 ∧ ∀ i, (g i * a i).totalDegree ≤ d

/-- Substituting polynomials of degree at most one does not raise the degree. -/
theorem totalDegree_bind₁_le {σ τ : Type*} (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℚ) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  have h : bind₁ f p = ∑ s ∈ p.support, bind₁ f (monomial s (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [h]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_totalDegree hs)
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hf i))

/-- If a substitution of degree one sends every equation of one system to a multiple of an
equation of another, a refutation of the first gives a refutation of the second of no larger
degree. -/
theorem NSRefutation.transfer {ι ι' σ σ' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    {a : ι → MvPolynomial σ ℚ} {b : ι' → MvPolynomial σ' ℚ} {d : ℕ}
    (f : σ → MvPolynomial σ' ℚ) (hf : ∀ i, (f i).totalDegree ≤ 1) (π : ι → ι')
    (c : ι → MvPolynomial σ' ℚ) (hc : ∀ i, bind₁ f (a i) = c i * b (π i))
    (h : NSRefutation a d) : NSRefutation b d := by
  obtain ⟨g, hg, hd⟩ := h
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => π i = j), bind₁ f (g i) * c i, ?_, ?_⟩
  · have h1 : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => π i = j), bind₁ f (g i) * c i) * b j
        = ∑ i ∈ Finset.univ.filter (fun i => π i = j), bind₁ f (g i * a i) := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, hc i, (Finset.mem_filter.mp hi).2]
      ring
    simp only [h1]
    rw [Finset.sum_fiberwise, ← map_sum, hg, map_one]
  · intro j
    have h1 : (∑ i ∈ Finset.univ.filter (fun i => π i = j), bind₁ f (g i) * c i) * b j
        = ∑ i ∈ Finset.univ.filter (fun i => π i = j), bind₁ f (g i * a i) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, hc i, (Finset.mem_filter.mp hi).2]
      ring
    rw [h1]
    exact totalDegree_finsetSum_le fun i _ => (totalDegree_bind₁_le f hf _).trans (hd i)

variable {n m : ℕ}

/-- The polynomial of a literal that vanishes when the literal is true. -/
noncomputable def literalAxiom (l : Literal n) : MvPolynomial (Fin n) ℚ :=
  if l.positive then 1 - X l.var else X l.var

/-- The usual equations of a 3CNF formula: `X i ^ 2 - X i` for every variable, and for every
clause the product over its literals of the polynomial that vanishes when the literal is
true. -/
noncomputable def formulaAxioms (φ : Fin m → Clause n) :
    Fin n ⊕ Fin m → MvPolynomial (Fin n) ℚ
  | Sum.inl i => X i ^ 2 - X i
  | Sum.inr j => ∏ k, literalAxiom (φ j k)

/-- The equations "the map of the reduction is zero", with rational coefficients. -/
noncomputable def kellerAxioms (φ : Fin m → Clause n) : Var n m → MvPolynomial (Var n m) ℚ :=
  fun a => map (Int.castRingHom ℚ) (reductionMap φ a)

/-- The substitution: a variable block goes to the line through its two points, a clause block
to the point `(0, 0, -1/4)`. -/
noncomputable def blockPoint : Var n m → MvPolynomial (Fin n) ℚ
  | (Sum.inl i, k) => (![X i, C (-3 / 2) * X i, C (-1 / 4) + C (27 / 4) * X i] :
      Fin 3 → MvPolynomial (Fin n) ℚ) k
  | (Sum.inr _, k) => (![0, 0, C (-1 / 4)] : Fin 3 → MvPolynomial (Fin n) ℚ) k

theorem totalDegree_blockPoint (a : Var n m) : (blockPoint a).totalDegree ≤ 1 := by
  obtain ⟨b | b, k⟩ := a
  · fin_cases k
    · exact Deg.var _
    · change (C (-3 / 2) * X b : MvPolynomial (Fin n) ℚ).totalDegree ≤ 1
      exact le_trans (by td) (by norm_num)
    · change (C (-1 / 4) + C (27 / 4) * X b : MvPolynomial (Fin n) ℚ).totalDegree ≤ 1
      exact le_trans (by td) (by norm_num)
  · fin_cases k
    · exact totalDegree_zero.le.trans (by norm_num)
    · exact totalDegree_zero.le.trans (by norm_num)
    · exact (Deg.const _).trans (by norm_num)

theorem map_poly (k : Fin 3) : map (Int.castRingHom ℚ) (poly ℤ k) = poly ℚ k := by
  fin_cases k <;> simp [poly, map_ofNat]

theorem map_gadgetAt (b : Fin n ⊕ Fin m) (k : Fin 3) :
    map (Int.castRingHom ℚ) (gadgetAt b k)
      = 12 * rename (fun j => ((b, j) : Var n m)) (poly ℚ k)
        + (![3, 0, 0] : Fin 3 → MvPolynomial (Var n m) ℚ) k := by
  rw [gadgetAt, map_add, map_mul, map_ofNat, map_rename, map_poly]
  congr 1
  fin_cases k <;> simp [map_ofNat]

/-- What the substitution leaves of the three equations of a variable block: a multiple of the
Boolean equation. -/
noncomputable def variableQuotient (i : Fin n) : Fin 3 → MvPolynomial (Fin n) ℚ :=
  ![C (-2187 / 8) * X i ^ 5 - 81 * X i ^ 4 + C (1863 / 4) * X i ^ 3 + 162 * X i ^ 2
      - C (405 / 2) * X i - 81,
    C (2187 / 4) * X i ^ 4 + 162 * X i ^ 3 - 567 * X i ^ 2 - 216 * X i + 27,
    -81 * X i ^ 2 - 24 * X i - 24]

theorem bind₁_kellerAxioms_inl (φ : Fin m → Clause n) (i : Fin n) (k : Fin 3) :
    bind₁ blockPoint (kellerAxioms φ (Sum.inl i, k))
      = variableQuotient i k * (X i ^ 2 - X i) := by
  apply MvPolynomial.funext
  intro v
  fin_cases k <;>
    simp [kellerAxioms, reductionMap, map_gadgetAt, poly, blockPoint, variableQuotient,
      map_ofNat] <;> ring

/-- The factor that the substitution leaves next to the product of a clause. -/
noncomputable def literalCofactor (l : Literal n) : MvPolynomial (Fin n) ℚ :=
  if l.positive then 1 + X l.var else X l.var

theorem bind₁_literal (l : Literal n) :
    bind₁ blockPoint (map (Int.castRingHom ℚ) (1 - literalPoly (m := m) l))
      = literalCofactor l * literalAxiom l := by
  unfold literalPoly literalCofactor literalAxiom
  split_ifs <;> simp [blockPoint] <;> ring

theorem bind₁_kellerAxioms_inr (φ : Fin m → Clause n) (j : Fin m) (k : Fin 3) :
    bind₁ blockPoint (kellerAxioms φ (Sum.inr j, k))
      = (-(![7, 24, 8] : Fin 3 → MvPolynomial (Fin n) ℚ) k * ∏ l, literalCofactor (φ j l))
        * ∏ l, literalAxiom (φ j l) := by
  have hg : bind₁ blockPoint (map (Int.castRingHom ℚ) (gadgetAt (n := n) (m := m) (Sum.inr j) k))
      = 0 := by
    apply MvPolynomial.funext
    intro v
    fin_cases k <;>
      simp [map_gadgetAt, poly, blockPoint, map_ofNat]
    norm_num
  have hc : bind₁ blockPoint (map (Int.castRingHom ℚ) (1 - clausePoly (m := m) (φ j)))
      = (∏ l, literalCofactor (φ j l)) * ∏ l, literalAxiom (φ j l) := by
    have : (1 : MvPolynomial (Var n m) ℤ) - clausePoly (φ j) = ∏ l, (1 - literalPoly (φ j l)) := by
      simp [clausePoly]
    rw [this, map_prod, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => bind₁_literal (φ j l)
  have h7 : bind₁ blockPoint (map (Int.castRingHom ℚ)
      ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k))
        = (![7, 24, 8] : Fin 3 → MvPolynomial (Fin n) ℚ) k := by
    fin_cases k <;> simp [map_ofNat]
  have hrm : kellerAxioms φ (Sum.inr j, k)
      = map (Int.castRingHom ℚ) (gadgetAt (Sum.inr j) k)
        - map (Int.castRingHom ℚ) (1 - clausePoly (φ j))
          * map (Int.castRingHom ℚ) ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k) := by
    simp only [kellerAxioms, reductionMap]
    rw [map_sub, map_mul]
  rw [hrm, map_sub, map_mul, hg, hc, h7]
  ring

/-- **A refutation of the map is a refutation of the formula.** A Nullstellensatz refutation of
degree `d` of the equations "the map of the reduction of `φ` is zero" gives one of degree at
most `d` of the equations of `φ`. -/
theorem refutation_of_formula (φ : Fin m → Clause n) (d : ℕ)
    (h : NSRefutation (kellerAxioms φ) d) : NSRefutation (formulaAxioms φ) d := by
  refine h.transfer blockPoint totalDegree_blockPoint
    Prod.fst
    (fun a => match a with
      | (Sum.inl i, k) => variableQuotient i k
      | (Sum.inr j, k) =>
        -(![7, 24, 8] : Fin 3 → MvPolynomial (Fin n) ℚ) k * ∏ l, literalCofactor (φ j l)) ?_
  rintro ⟨i | j, k⟩
  · simpa [formulaAxioms] using bind₁_kellerAxioms_inl φ i k
  · simpa [formulaAxioms] using bind₁_kellerAxioms_inr φ j k

end KellerZero
