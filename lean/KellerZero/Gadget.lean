import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The three-variable Keller gadget

The polynomial map `F = (P, Q, R)` below is the explicit three-variable map announced by
L. Alpöge (19 July 2026) and used, after an affine rescaling, by L. Stambler in
"Reducing 3SAT to Zero-Finding for Constant-Jacobian Polynomial Maps"
(https://github.com/Lev-Stambler/alg-geom-TCS).

Checked here, over every field of characteristic zero unless said otherwise:

* `det_jacobian`: the Jacobian determinant of `F` is the constant `-2` (over every commutative
  ring, as an identity of polynomials);
* `not_injective`: `F` takes the value `(-1/4, 0, 0)` at three different points;
* `jacobian_conjecture_fails_dim_three`: the two facts together, as one statement;
* `fibre_zero`: the fibre over `(-1/4, 0, 0)` is exactly those three points;
* `omitted_curve`: no point of the curve `t ↦ (t ^ 2 / 12, t, 4 / (3 t))`, `t ≠ 0`, is a value
  of `F` (`H_omitted_curve` is the same in the coordinates of the reduction);
* `exists_zero_iff_satisfiable`: the system of equations of Stambler's reduction has a solution
  exactly when the 3CNF formula is satisfiable;
* `hitsTarget_iff_satisfiable`: the same with one map for all formulas on a list of clauses,
  the formula entering only through the target.

Not checked here: that the Jacobian determinant of the big map of the reduction is constant
(it is block triangular with copies of the gadget on the diagonal), and that the curve of
`omitted_curve` is the whole set of omitted values over the complex numbers.
-/

namespace KellerZero

section Functions

variable {K : Type*} [Field K]

/-- First coordinate of the map. -/
def P (x y z : K) : K := (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

/-- Second coordinate of the map. -/
def Q (x y z : K) : K := y + 3 * x * (1 + x * y) ^ 2 * z + 3 * x * y ^ 2 * (4 + 3 * x * y)

/-- Third coordinate of the map. -/
def R (x y z : K) : K := 2 * x - 3 * x ^ 2 * y - x ^ 3 * z

/-- The map takes the same value at three different points. -/
theorem three_points [CharZero K] :
    (P (0 : K) 0 (-1 / 4) = -1 / 4 ∧ Q (0 : K) 0 (-1 / 4) = 0 ∧ R (0 : K) 0 (-1 / 4) = 0) ∧
    (P (1 : K) (-3 / 2) (13 / 2) = -1 / 4 ∧ Q (1 : K) (-3 / 2) (13 / 2) = 0 ∧
      R (1 : K) (-3 / 2) (13 / 2) = 0) ∧
    (P (-1 : K) (3 / 2) (13 / 2) = -1 / 4 ∧ Q (-1 : K) (3 / 2) (13 / 2) = 0 ∧
      R (-1 : K) (3 / 2) (13 / 2) = 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> simp only [P, Q, R] <;> norm_num

/-- The fibre over `(-1/4, 0, 0)` is exactly the three points of `three_points`. -/
theorem fibre_zero [CharZero K] (x y z : K)
    (hP : P x y z = -1 / 4) (hQ : Q x y z = 0) (hR : R x y z = 0) :
    (x = 0 ∧ y = 0 ∧ z = -1 / 4) ∨ (x = 1 ∧ y = -3 / 2 ∧ z = 13 / 2) ∨
      (x = -1 ∧ y = 3 / 2 ∧ z = 13 / 2) := by
  have hP4 : 4 * P x y z = -1 := by rw [hP]; norm_num
  simp only [P, Q, R] at hP4 hQ hR
  have hA : 4 * (1 + x * y) * ((1 + x * y) - 1) = 3 * x ^ 2 := by
    linear_combination 4 * x * (1 + x * y) * hQ - 3 * x ^ 2 * hP4
  have hB : x * (4 * (1 + x * y) * ((1 + x * y) + 1) + x ^ 2) = 0 := by
    linear_combination 4 * (1 + x * y) ^ 3 * hR + x ^ 3 * hP4
  by_cases hx : x = 0
  · left
    subst hx
    have hy : y = 0 := by linear_combination hQ
    subst hy
    refine ⟨rfl, rfl, ?_⟩
    linear_combination hP4 / 4
  · right
    have hC : 4 * (1 + x * y) * ((1 + x * y) + 1) + x ^ 2 = 0 := by
      rcases mul_eq_zero.mp hB with h | h
      · exact absurd h hx
      · exact h
    have hD : (1 + x * y) * (2 * (1 + x * y) + 1) = 0 := by
      linear_combination hA / 8 + 3 * hC / 8
    have hu : 2 * (1 + x * y) + 1 = 0 := by
      rcases mul_eq_zero.mp hD with h | h
      · exfalso
        have h0 := hP4
        rw [show (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)
          = (1 + x * y) * ((1 + x * y) ^ 2 * z + y ^ 2 * (4 + 3 * x * y)) by ring, h] at h0
        simp at h0
      · exact h
    have hxy : x * y = -3 / 2 := by linear_combination hu / 2
    have hx2 : (x - 1) * (x + 1) = 0 := by
      linear_combination hC - (2 * (1 + x * y) + 1) * hu
    rcases mul_eq_zero.mp hx2 with h | h
    · left
      have hx1 : x = 1 := by linear_combination h
      subst hx1
      have hy : y = -3 / 2 := by linear_combination hxy
      subst hy
      refine ⟨rfl, rfl, ?_⟩
      linear_combination -2 * hP4
    · right
      have hx1 : x = -1 := by linear_combination h
      subst hx1
      have hy : y = 3 / 2 := by linear_combination -hxy
      subst hy
      refine ⟨rfl, rfl, ?_⟩
      linear_combination -2 * hP4

/-- No point of the curve `t ↦ (t ^ 2 / 12, t, 4 / (3 t))`, `t ≠ 0`, is a value of the map. -/
theorem omitted_curve [CharZero K] (t : K) (ht : t ≠ 0) (x y z : K) :
    ¬ (P x y z = t ^ 2 / 12 ∧ Q x y z = t ∧ R x y z = 4 / (3 * t)) := by
  rintro ⟨hP, hQ, hR⟩
  have hP' : 12 * P x y z = t ^ 2 := by rw [hP]; ring
  have hR' : 3 * t * R x y z = 4 := by rw [hR]; field_simp
  simp only [P, Q, R] at hP' hQ hR'
  have h1 : (t * x - 2 * (1 + x * y)) ^ 2 = 4 * (1 + x * y) := by
    linear_combination 4 * x * (1 + x * y) * hQ - x ^ 2 * hP'
  have h2 : (t * x) ^ 3 - 12 * (t * x) * (1 + x * y) * ((1 + x * y) + 1)
      + 16 * (1 + x * y) ^ 3 = 0 := by
    linear_combination (-(t * x ^ 3)) * hP' - 4 * (1 + x * y) ^ 3 * hR'
  have h3 : (1 + x * y) * (t * x - 2 * (1 + x * y)) = 0 := by
    linear_combination (6 * (1 + x * y) + (t * x - 2 * (1 + x * y))) / 8 * h1 - h2 / 8
  have hu : 1 + x * y = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · rw [h] at h1
      linear_combination -h1 / 4
  have : t ^ 2 = 0 := by
    rw [← hP', show (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)
      = (1 + x * y) * ((1 + x * y) ^ 2 * z + y ^ 2 * (4 + 3 * x * y)) by ring, hu]
    ring
  exact ht (pow_eq_zero_iff (by norm_num) |>.mp this)

end Functions

section Polynomials

open MvPolynomial

variable (A : Type*) [CommRing A]

/-- The map as three polynomials in three variables, over any commutative ring. -/
noncomputable def poly : Fin 3 → MvPolynomial (Fin 3) A :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * X 0 * X 1),
    X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * X 0 * X 1),
    2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

/-- The Jacobian matrix of the map: entry `(i, j)` is the derivative of coordinate `i` in
variable `j`. -/
noncomputable def jacobian : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) A) :=
  Matrix.of fun i j => pderiv j (poly A i)

/-- The derivative of a numeral is zero. -/
theorem pderiv_ofNat {σ : Type*} (i : σ) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ A) = 0 := by
  rw [← Nat.cast_ofNat (R := MvPolynomial σ A)]
  exact Derivation.map_natCast _ n

/-- The Jacobian determinant is the constant `-2`. -/
theorem det_jacobian : (jacobian A).det = C (-2) := by
  have hC : (C (-2) : MvPolynomial (Fin 3) A) = -2 := by rw [map_neg, map_ofNat]
  rw [hC, Matrix.det_fin_three]
  simp only [jacobian, poly, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub,
    Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_X, pderiv_one, pderiv_ofNat, Pi.single_apply, smul_eq_mul, nsmul_eq_mul]
  simp
  ring

/-- Evaluating the polynomials gives the functions `P`, `Q`, `R`. -/
theorem eval_poly {K : Type*} [Field K] (v : Fin 3 → K) :
    (fun i => eval v (poly K i)) = ![P (v 0) (v 1) (v 2), Q (v 0) (v 1) (v 2), R (v 0) (v 1) (v 2)] := by
  funext i
  fin_cases i <;> simp [poly, P, Q, R]

/-- A polynomial map of three-space, over any field of characteristic zero, whose Jacobian
determinant is a nonzero constant and which is not injective. So it has no inverse of any kind,
and the Jacobian conjecture fails in dimension three. -/
theorem jacobian_conjecture_fails_dim_three (K : Type*) [Field K] [CharZero K] :
    ∃ F : Fin 3 → MvPolynomial (Fin 3) K,
      (Matrix.of fun i j => pderiv j (F i)).det = C (-2) ∧
      ¬ Function.Injective fun v : Fin 3 → K => fun i => eval v (F i) := by
  refine ⟨poly K, det_jacobian K, fun hinj => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, -⟩ := three_points (K := K)
  have h : (![0, 0, -1 / 4] : Fin 3 → K) = ![1, -3 / 2, 13 / 2] := by
    apply hinj
    simp only [eval_poly, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, a1, a2, a3, b1, b2, b3]
  have h0 := congrFun h 0
  simp at h0

end Polynomials

section Reduction

variable {K : Type*} [Field K]

/-- The rescaled map of the reduction: `H = 12 F + (3, 0, 0)`. -/
def H (v : K × K × K) : K × K × K :=
  (12 * P v.1 v.2.1 v.2.2 + 3, 12 * Q v.1 v.2.1 v.2.2, 12 * R v.1 v.2.1 v.2.2)

/-- The zeros of `H` are three points; their first coordinates are `0`, `1` and `-1`. -/
theorem H_eq_zero_iff [CharZero K] (v : K × K × K) :
    H v = (0, 0, 0) ↔
      v = (0, 0, -1 / 4) ∨ v = (1, -3 / 2, 13 / 2) ∨ v = (-1, 3 / 2, 13 / 2) := by
  obtain ⟨x, y, z⟩ := v
  constructor
  · intro h
    simp only [H, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hP : P x y z = -1 / 4 := by linear_combination h1 / 12
    have hQ : Q x y z = 0 := by linear_combination h2 / 12
    have hR : R x y z = 0 := by linear_combination h3 / 12
    rcases fibre_zero x y z hP hQ hR with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp
  · rintro (h | h | h) <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp only [H, P, Q, R, Prod.mk.injEq] <;> norm_num

/-- The target `(7, 24, 8)` is not a value of `H`. -/
theorem H_ne_target [CharZero K] (v : K × K × K) : H v ≠ (7, 24, 8) := by
  obtain ⟨x, y, z⟩ := v
  intro h
  simp only [H, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine omitted_curve (2 : K) two_ne_zero x y z ⟨?_, ?_, ?_⟩
  · linear_combination h1 / 12
  · linear_combination h2 / 12
  · linear_combination h3 / 12

/-- In the coordinates of `H`, the omitted curve is `t ↦ (t ^ 2 + 3, 12 t, 16 / t)`; the target
`(7, 24, 8)` is its point `t = 2`. -/
theorem H_omitted_curve [CharZero K] (t : K) (ht : t ≠ 0) (v : K × K × K) :
    H v ≠ (t ^ 2 + 3, 12 * t, 16 / t) := by
  obtain ⟨x, y, z⟩ := v
  intro h
  simp only [H, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine omitted_curve t ht x y z ⟨?_, ?_, ?_⟩
  · linear_combination h1 / 12
  · linear_combination h2 / 12
  · rw [show R x y z = 16 / t / 12 by linear_combination h3 / 12]
    field_simp
    norm_num

/-- A literal: a variable and a sign. -/
structure Literal (n : ℕ) where
  /-- The variable. -/
  var : Fin n
  /-- `true` for the variable itself, `false` for its negation. -/
  positive : Bool

/-- A clause of three literals. -/
abbrev Clause (n : ℕ) := Fin 3 → Literal n

/-- The literal is true under the assignment. -/
def Literal.Holds {n : ℕ} (l : Literal n) (σ : Fin n → Bool) : Prop := σ l.var = l.positive

/-- The polynomial value of a literal: the square of the first coordinate of its variable's
block, or one minus it. -/
def Literal.value {n : ℕ} (l : Literal n) (w : Fin n → K × K × K) : K :=
  if l.positive then (w l.var).1 ^ 2 else 1 - (w l.var).1 ^ 2

/-- The satisfaction polynomial of a clause. -/
def clauseValue {n : ℕ} (c : Clause n) (w : Fin n → K × K × K) : K :=
  1 - ∏ k, (1 - (c k).value w)

open Classical in
/-- The assignment read off from variable blocks: a variable is true when the first coordinate
of its block is not zero. -/
noncomputable def decode {n : ℕ} (w : Fin n → K × K × K) : Fin n → Bool :=
  fun i => decide ((w i).1 ≠ 0)

/-- The variable blocks that store an assignment. -/
def encode {n : ℕ} (σ : Fin n → Bool) : Fin n → K × K × K :=
  fun i => if σ i then (1, -3 / 2, 13 / 2) else (0, 0, -1 / 4)

theorem H_encode [CharZero K] {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    H (encode (K := K) σ i) = (0, 0, 0) := by
  apply (H_eq_zero_iff _).mpr
  cases h : σ i <;> simp [encode, h]

theorem decode_encode [CharZero K] {n : ℕ} (σ : Fin n → Bool) :
    decode (encode (K := K) σ) = σ := by
  funext i
  cases h : σ i <;> simp [decode, encode, h]

/-- At zeros of `H`, the value of a literal is `1` when it holds and `0` when it does not. -/
theorem value_eq [CharZero K] {n : ℕ} {w : Fin n → K × K × K} (hw : ∀ i, H (w i) = (0, 0, 0))
    (l : Literal n) : (l.Holds (decode w) → l.value w = 1) ∧ (¬ l.Holds (decode w) → l.value w = 0) := by
  have h3 := (H_eq_zero_iff (w l.var)).mp (hw l.var)
  cases hl : l.positive <;>
    rcases h3 with h | h | h <;> simp [Literal.value, Literal.Holds, decode, hl, h]

/-- At zeros of `H`, a clause with a true literal has value `1`. -/
theorem clauseValue_of_holds [CharZero K] {n : ℕ} {w : Fin n → K × K × K}
    (hw : ∀ i, H (w i) = (0, 0, 0)) (c : Clause n) (h : ∃ k, (c k).Holds (decode w)) :
    clauseValue c w = 1 := by
  obtain ⟨k, hk⟩ := h
  have hk1 : (1 : K) - (c k).value w = 0 := by rw [(value_eq hw (c k)).1 hk, sub_self]
  have hprod : ∏ k', ((1 : K) - (c k').value w) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk1
  simp [clauseValue, hprod]

/-- At zeros of `H`, a clause with no true literal has value `0`. -/
theorem clauseValue_of_not_holds [CharZero K] {n : ℕ} {w : Fin n → K × K × K}
    (hw : ∀ i, H (w i) = (0, 0, 0)) (c : Clause n) (h : ¬ ∃ k, (c k).Holds (decode w)) :
    clauseValue c w = 0 := by
  have : ∀ k, (1 : K) - (c k).value w = 1 := by
    intro k
    rw [(value_eq hw (c k)).2 (fun hk => h ⟨k, hk⟩), sub_zero]
  simp [clauseValue, this]

/-- `(w, v)` is a zero of the map of the reduction for the formula `φ`: every variable block
is a zero of `H`, and every clause block `v j` satisfies `H (v j) = (1 - s_j(w)) (7, 24, 8)`. -/
def IsZero {n m : ℕ} (φ : Fin m → Clause n) (w : Fin n → K × K × K)
    (v : Fin m → K × K × K) : Prop :=
  (∀ i, H (w i) = (0, 0, 0)) ∧
    ∀ j, H (v j) = ((1 - clauseValue (φ j) w) * 7, (1 - clauseValue (φ j) w) * 24,
      (1 - clauseValue (φ j) w) * 8)

/-- The map of the reduction has a zero exactly when the formula is satisfiable. -/
theorem exists_zero_iff_satisfiable [CharZero K] {n m : ℕ} (φ : Fin m → Clause n) :
    (∃ (w : Fin n → K × K × K) (v : Fin m → K × K × K), IsZero φ w v) ↔
      ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ := by
  constructor
  · rintro ⟨w, v, hw, hv⟩
    refine ⟨decode w, fun j => ?_⟩
    by_contra hno
    have := hv j
    rw [clauseValue_of_not_holds hw (φ j) hno] at this
    exact H_ne_target (v j) (by simpa using this)
  · rintro ⟨σ, hσ⟩
    refine ⟨encode σ, fun _ => (0, 0, -1 / 4), H_encode σ, fun j => ?_⟩
    rw [clauseValue_of_holds (H_encode σ) (φ j) (by rw [decode_encode]; exact hσ j)]
    simpa using (H_eq_zero_iff ((0 : K), (0 : K), (-1 / 4 : K))).mpr (Or.inl rfl)

/-- `(w, lam, v)` is sent to the target of the selection `sel` by the one map built from the
list `cs` of clauses: variable blocks go to zero, the coordinate `lam c` is the identity and
must equal `1` on selected clauses and `0` on the others, and the clause block `v c` satisfies
`H (v c) = lam c * (1 - s_c(w)) (7, 24, 8)`. The map does not depend on `sel`; only the target
does. -/
def HitsTarget {n M : ℕ} (cs : Fin M → Clause n) (sel : Fin M → Bool)
    (w : Fin n → K × K × K) (lam : Fin M → K) (v : Fin M → K × K × K) : Prop :=
  (∀ i, H (w i) = (0, 0, 0)) ∧ (∀ c, lam c = if sel c then 1 else 0) ∧
    ∀ c, H (v c) = (lam c * (1 - clauseValue (cs c) w) * 7,
      lam c * (1 - clauseValue (cs c) w) * 24, lam c * (1 - clauseValue (cs c) w) * 8)

/-- One fixed map, many formulas: the target of a selection of clauses is a value of the map
exactly when the selected clauses are satisfiable together. -/
theorem hitsTarget_iff_satisfiable [CharZero K] {n M : ℕ} (cs : Fin M → Clause n)
    (sel : Fin M → Bool) :
    (∃ (w : Fin n → K × K × K) (lam : Fin M → K) (v : Fin M → K × K × K),
        HitsTarget cs sel w lam v) ↔
      ∃ σ : Fin n → Bool, ∀ c, sel c = true → ∃ k, (cs c k).Holds σ := by
  constructor
  · rintro ⟨w, lam, v, hw, hl, hv⟩
    refine ⟨decode w, fun c hc => ?_⟩
    by_contra hno
    have := hv c
    rw [clauseValue_of_not_holds hw (cs c) hno, hl c, hc] at this
    exact H_ne_target (v c) (by simpa using this)
  · rintro ⟨σ, hσ⟩
    refine ⟨encode σ, fun c => if sel c then 1 else 0, fun _ => (0, 0, -1 / 4), H_encode σ,
      fun _ => rfl, fun c => ?_⟩
    have h0 := (H_eq_zero_iff ((0 : K), (0 : K), (-1 / 4 : K))).mpr (Or.inl rfl)
    cases hc : sel c
    · simpa [hc] using h0
    · rw [clauseValue_of_holds (H_encode σ) (cs c) (by rw [decode_encode]; exact hσ c hc)]
      simpa [hc] using h0

end Reduction

end KellerZero
