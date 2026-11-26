import KellerZero.Open
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# O3: a map of degree at most two with constant Jacobian determinant is injective

Wang's argument (1980). Suppose `F a = F b`. Restrict every coordinate of `F` to the line
through the midpoint `c = (a + b) / 2` in the direction `h = (b - a) / 2`. It becomes a
polynomial of degree at most two in one variable taking the same value at `1` and `-1`, so its
derivative at `0` vanishes. By the chain rule that derivative is row `i` of the Jacobian matrix
at `c` applied to `h`. The Jacobian matrix at `c` is invertible, so `h = 0`.
-/

namespace KellerZero.Proofs.Quadratic

variable {N : ℕ}

/-- The line `s ↦ c + s h`, as polynomials in `s`. -/
noncomputable def line (c h : Fin N → ℚ) (j : Fin N) : Polynomial ℚ :=
  Polynomial.C (c j) + Polynomial.C (h j) * Polynomial.X

theorem natDegree_line_le (c h : Fin N → ℚ) (j : Fin N) : (line c h j).natDegree ≤ 1 := by
  unfold line
  compute_degree

/-- Restricting to the line and then evaluating at `s` is evaluating at `c + s h`. -/
theorem eval_aeval_line (c h : Fin N → ℚ) (s : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    Polynomial.eval s (MvPolynomial.aeval (line c h) p)
      = MvPolynomial.eval (fun j => c j + h j * s) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, line]

/-- The chain rule along the line. -/
theorem derivative_aeval_line (c h : Fin N → ℚ) (p : MvPolynomial (Fin N) ℚ) :
    Polynomial.derivative (MvPolynomial.aeval (line c h) p)
      = ∑ j, Polynomial.C (h j) * MvPolynomial.aeval (line c h) (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Polynomial.derivative_mul, hp,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, Pi.single_apply]
    have hline : Polynomial.derivative (line c h i) = Polynomial.C (h i) := by
      simp [line]
    rw [hline, Finset.sum_mul]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_comm]

/-- A polynomial of degree at most two: the difference of its values at `1` and `-1` is twice
its derivative at `0`. -/
theorem eval_one_sub_eval_neg_one (g : Polynomial ℚ) (hg : g.natDegree ≤ 2) :
    g.eval 1 - g.eval (-1) = 2 * (Polynomial.derivative g).eval 0 := by
  have h := Polynomial.eq_quadratic_of_degree_le_two (Polynomial.natDegree_le_iff_degree_le.mp hg)
  generalize g.coeff 2 = a2 at h
  generalize g.coeff 1 = a1 at h
  generalize g.coeff 0 = a0 at h
  subst h
  simp
  ring

end KellerZero.Proofs.Quadratic

open KellerZero.Proofs.Quadratic in
theorem KellerZero.Proofs.QuadraticKellerMapsAreInjective :
    KellerZero.Open.QuadraticKellerMapsAreInjective := by
  intro N F hdeg hunit a b hab
  -- the midpoint and half the difference
  obtain ⟨c, hc⟩ : ∃ c : Fin N → ℚ, c = fun j => (a j + b j) / 2 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Fin N → ℚ, h = fun j => (b j - a j) / 2 := ⟨_, rfl⟩
  have hb : (fun j => c j + h j * 1) = b := by funext j; simp [hc, hh]; ring
  have ha : (fun j => c j + h j * (-1)) = a := by funext j; simp [hc, hh]; ring
  have hc0 : (fun j => c j + h j * 0) = c := by funext j; simp
  -- every row of the Jacobian matrix at `c` kills `h`
  have hrow : ∀ i, ∑ j, MvPolynomial.eval c (MvPolynomial.pderiv j (F i)) * h j = 0 := by
    intro i
    have hnat : (MvPolynomial.aeval (line c h) (F i)).natDegree ≤ 2 * 1 :=
      MvPolynomial.aeval_natDegree_le (F i) (hdeg i) (line c h) (natDegree_line_le c h)
    have hq := eval_one_sub_eval_neg_one _ hnat
    rw [eval_aeval_line, eval_aeval_line, hb, ha, derivative_aeval_line] at hq
    have hi : MvPolynomial.eval a (F i) = MvPolynomial.eval b (F i) := congrFun hab i
    rw [hi, sub_self] at hq
    have hsum : Polynomial.eval 0 (∑ j, Polynomial.C (h j)
        * MvPolynomial.aeval (line c h) (MvPolynomial.pderiv j (F i)))
        = ∑ j, MvPolynomial.eval c (MvPolynomial.pderiv j (F i)) * h j := by
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, eval_aeval_line, hc0, mul_comm]
    rw [hsum] at hq
    linarith
  -- the Jacobian matrix at `c` is invertible
  have hdet : ((Matrix.of fun i j => MvPolynomial.pderiv j (F i)).map (MvPolynomial.eval c)).det ≠ 0 := by
    have := hunit.map (MvPolynomial.eval c)
    rw [RingHom.map_det] at this
    exact this.ne_zero
  have hzero : h = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    simpa [Matrix.mulVec, dotProduct] using hrow i
  funext j
  have := congrFun hzero j
  rw [hh] at this
  simp only [Pi.zero_apply] at this
  linarith
