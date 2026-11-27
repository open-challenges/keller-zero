import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Wire extensions: lowering the degree of a map without changing its Jacobian determinant

Let `F` be a polynomial map in the variables `ι`. Add variables `t c`, one for every *wire*
`c : κ`, choose polynomials `s c = t c + (a polynomial in the old variables and in the wires
before c)` and polynomials `p j` in the `s c` alone, and put

    G = ( F j - p j (s),  s c ).

This is the reduction of degree of Bass, Connell and Wright (1982) in the form used for the
explicit maps of this repository: `G = T ∘ (F × id) ∘ S` with `S (x, t) = (x, s (x, t))` and
`T (a, s) = (a - p s, s)`.

* `pderiv_bind₁`: the chain rule for substitution of polynomials into a polynomial;
* `det_wireExt`: the Jacobian determinant of `G` is the Jacobian determinant of `F`;
* `aeval_wireExt_eq_zero_iff`: if the `p j` have no constant term, a point `(x, t)` is a zero
  of `G` exactly when `x` is a zero of `F` and every `s c` vanishes at `(x, t)`.

The choice of the `s c` and `p j` is what makes the degree of `G` small; nothing here depends
on it.
-/

namespace KellerZero

open MvPolynomial

section ChainRule

variable {R : Type*} [CommRing R] {σ τ : Type*} [Fintype σ]

/-- The chain rule: the derivative of `p (f)` is the sum over the variables `i` of `p` of
`(∂p/∂i) (f)` times the derivative of `f i`. -/
theorem pderiv_bind₁ (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (k : τ) :
    pderiv k (bind₁ f p) = ∑ i, bind₁ f (pderiv i p) * pderiv k (f i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, bind₁_X_right, pderiv_mul, hp, pderiv_X, map_add, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [apply_ite (bind₁ f), ite_mul]

end ChainRule

section Wire

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- The wire extension of the map `F` by the wires `s` carrying the polynomials `p`. -/
noncomputable def wireExt (F : ι → MvPolynomial ι R) (s : κ → MvPolynomial (ι ⊕ κ) R)
    (p : ι → MvPolynomial κ R) : ι ⊕ κ → MvPolynomial (ι ⊕ κ) R :=
  Sum.elim (fun j => rename Sum.inl (F j) - bind₁ s (p j)) s

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem pderiv_inr_rename_inl (f : MvPolynomial ι R) (k : κ) :
    pderiv (Sum.inr k : ι ⊕ κ) (rename Sum.inl f) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  have := (vars_rename _ _) h
  simp at this

/-- The Jacobian determinant of a wire extension is the Jacobian determinant of the map, as long
as every wire is its own variable plus a polynomial in the old variables and in wires of lower
rank. -/
theorem det_wireExt (F : ι → MvPolynomial ι R) (s : κ → MvPolynomial (ι ⊕ κ) R)
    (p : ι → MvPolynomial κ R) (rank : κ → ℕ)
    (h1 : ∀ c, pderiv (Sum.inr c) (s c) = 1)
    (h2 : ∀ c d, c ≠ d → rank c ≤ rank d → pderiv (Sum.inr d) (s c) = 0) :
    (Matrix.of fun a b => pderiv b (wireExt F s p a)).det
      = rename Sum.inl (Matrix.of fun i j => pderiv j (F i)).det := by
  set A : Matrix ι κ (MvPolynomial (ι ⊕ κ) R) := Matrix.of fun i c => bind₁ s (pderiv c (p i))
    with hA
  set Sx : Matrix κ ι (MvPolynomial (ι ⊕ κ) R) := Matrix.of fun c k => pderiv (Sum.inl k) (s c)
    with hSx
  set St : Matrix κ κ (MvPolynomial (ι ⊕ κ) R) := Matrix.of fun c k => pderiv (Sum.inr k) (s c)
    with hSt
  set JF : Matrix ι ι (MvPolynomial (ι ⊕ κ) R) :=
    Matrix.of fun i k => rename Sum.inl (pderiv k (F i)) with hJF
  have hM : (Matrix.of fun a b => pderiv b (wireExt F s p a))
      = Matrix.fromBlocks 1 (-A) 0 1 * Matrix.fromBlocks JF 0 Sx St := by
    rw [Matrix.fromBlocks_multiply]
    ext (i | c) (k | k)
    · simp [wireExt, pderiv_bind₁, Matrix.mul_apply, hA, hSx, hJF,
        pderiv_rename Sum.inl_injective, sub_eq_add_neg]
    · simp [wireExt, pderiv_bind₁, Matrix.mul_apply, hA, hSt, pderiv_inr_rename_inl]
    · simp [wireExt, hSx]
    · simp [wireExt, hSt]
  have hSt1 : St.det = 1 := by
    have hT : St.BlockTriangular (OrderDual.toDual ∘ rank) := by
      intro c d hcd
      have hlt : rank c < rank d := hcd
      exact h2 c d (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt) hlt.le
    rw [hT.det]
    refine Finset.prod_eq_one fun a _ => ?_
    have : St.toSquareBlock (OrderDual.toDual ∘ rank) a = 1 := by
      refine Matrix.ext fun i j => ?_
      obtain ⟨c, hc⟩ := i
      obtain ⟨d, hd⟩ := j
      rw [Matrix.one_apply]
      change St c d = _
      by_cases hcd : c = d
      · subst hcd
        simp [hSt, h1]
      · have hr : rank c ≤ rank d := by
          have : OrderDual.toDual (rank c) = OrderDual.toDual (rank d) := hc.trans hd.symm
          exact (OrderDual.toDual.injective this).le
        simp [hSt, h2 c d hcd hr, hcd]
    rw [this, Matrix.det_one]
  have hJF1 : JF.det = rename Sum.inl (Matrix.of fun i j => pderiv j (F i)).det := by
    have : JF = (rename (R := R) (Sum.inl : ι → ι ⊕ κ)).toRingHom.mapMatrix
        (Matrix.of fun i j => pderiv j (F i)) := by
      ext i k
      simp [hJF]
    rw [this, ← RingHom.map_det]
    rfl
  rw [hM, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, hSt1, hJF1]
  simp

end Wire

section Zeros

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K] {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem aeval_wireExt_inl (F : ι → MvPolynomial ι R) (s : κ → MvPolynomial (ι ⊕ κ) R)
    (p : ι → MvPolynomial κ R) (x : ι → K) (t : κ → K) (j : ι) :
    aeval (Sum.elim x t) (wireExt F s p (Sum.inl j))
      = aeval x (F j) - aeval (fun c => aeval (Sum.elim x t) (s c)) (p j) := by
  simp [wireExt, aeval_rename, aeval_bind₁, Function.comp_def]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- A point is a zero of the wire extension exactly when its old coordinates are a zero of the
map and every wire vanishes there. -/
theorem aeval_wireExt_eq_zero_iff (F : ι → MvPolynomial ι R) (s : κ → MvPolynomial (ι ⊕ κ) R)
    (p : ι → MvPolynomial κ R) (hp : ∀ j, constantCoeff (p j) = 0) (x : ι → K) (t : κ → K) :
    (∀ a, aeval (Sum.elim x t) (wireExt F s p a) = 0)
      ↔ (∀ j, aeval x (F j) = 0) ∧ ∀ c, aeval (Sum.elim x t) (s c) = 0 := by
  constructor
  · intro h
    have hs : ∀ c, aeval (Sum.elim x t) (s c) = 0 := fun c => by simpa [wireExt] using h (Sum.inr c)
    refine ⟨fun j => ?_, hs⟩
    have hj := h (Sum.inl j)
    rw [aeval_wireExt_inl] at hj
    have h0 : (fun c => aeval (Sum.elim x t) (s c)) = (0 : κ → K) := funext hs
    rw [h0, aeval_zero, hp j, map_zero, sub_zero] at hj
    exact hj
  · rintro ⟨hF, hs⟩ (j | c)
    · rw [aeval_wireExt_inl]
      have h0 : (fun c => aeval (Sum.elim x t) (s c)) = (0 : κ → K) := funext hs
      rw [h0, aeval_zero, hp j, map_zero, sub_zero]
      exact hF j
    · simpa [wireExt] using hs c

end Zeros

end KellerZero
