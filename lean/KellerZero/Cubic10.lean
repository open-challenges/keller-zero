import KellerZero.Gadget
import KellerZero.Wire
import KellerZero.Degree

/-!
# The gadget at degree three, in ten variables

A map of degree three in ten variables with constant Jacobian determinant that is not injective:
a wire extension of the gadget with seven wires `d, k, a, h, e, q, s` (`Sum.inr 0 .. 6`) next to
`x, y, z` (`Sum.inl 0, 1, 2`). Found for this repository on 27 November 2026 by a search over
wire extensions; the smallest one published before it has eleven variables (`Cubic11.lean`).
The saving is the wire `k`, which stands for `x z + 3 y` and serves two coordinates:
`R = 2 x - x ^ 2 (x z + 3 y)`.

* `cubic10_eq`: the wire extension is the explicit map `cubic10` (three coordinates) followed by
  the seven wires;
* `det_cubic10Map`: its Jacobian determinant is the constant `-2`;
* `totalDegree_cubic10Map`: every coordinate has degree at most three;
* `cubic10Map_not_injective`: it takes the same value at two points, over every field of
  characteristic zero.
-/

namespace KellerZero

open MvPolynomial

/-- The variables of the ten-variable map. -/
abbrev V10 := Fin 3 ⊕ Fin 7

section Template

local notation "x₀" => (X (Sum.inl 0) : MvPolynomial V10 ℤ)
local notation "y₀" => (X (Sum.inl 1) : MvPolynomial V10 ℤ)
local notation "z₀" => (X (Sum.inl 2) : MvPolynomial V10 ℤ)
local notation "d₀" => (X (Sum.inr 0) : MvPolynomial V10 ℤ)
local notation "k₀" => (X (Sum.inr 1) : MvPolynomial V10 ℤ)
local notation "a₀" => (X (Sum.inr 2) : MvPolynomial V10 ℤ)
local notation "h₀" => (X (Sum.inr 3) : MvPolynomial V10 ℤ)
local notation "e₀" => (X (Sum.inr 4) : MvPolynomial V10 ℤ)
local notation "q₀" => (X (Sum.inr 5) : MvPolynomial V10 ℤ)
local notation "s₀" => (X (Sum.inr 6) : MvPolynomial V10 ℤ)

/-- The seven wires: each is its own variable plus a polynomial in `x, y, z` and earlier
wires. -/
noncomputable def wire10 : Fin 7 → MvPolynomial V10 ℤ :=
  ![d₀ - x₀ * y₀,
    k₀ - x₀ * z₀ - 3 * y₀,
    a₀ - d₀ ^ 2 + 2 * d₀ * x₀ * y₀,
    h₀ - x₀ ^ 2,
    e₀ - x₀ * y₀ * z₀ - 3 * y₀ ^ 2 - z₀,
    q₀ - 3 * x₀ * y₀ * k₀ - 3 * d₀ * k₀ - 6 * x₀ * z₀,
    s₀ - x₀ * y₀ * e₀ - 2 * x₀ * y₀ * z₀ - d₀ * e₀ + z₀ * a₀ - 2 * z₀ * d₀ - 7 * y₀ ^ 2]

/-- What the wires carry away from the three coordinates of the gadget. -/
noncomputable def carry10 : Fin 3 → MvPolynomial (Fin 7) ℤ :=
  ![-(X 2 * X 4) - X 0 ^ 2 * X 4 + X 0 * X 6,
    -(3 * X 2 * X 1) - 3 * X 0 ^ 2 * X 1 + X 0 * X 5,
    -(X 3 * X 1)]

/-- The first three coordinates of the ten-variable map. -/
noncomputable def cubic10 : Fin 3 → MvPolynomial V10 ℤ :=
  ![d₀ ^ 2 * e₀ - z₀ * d₀ * a₀ + 2 * z₀ * d₀ ^ 2 - 3 * y₀ ^ 2 * a₀ + 7 * y₀ ^ 2 * d₀
      + x₀ * y₀ * s₀ + 3 * x₀ * y₀ * z₀ + a₀ * e₀ - d₀ * s₀ - z₀ * a₀ + 4 * y₀ ^ 2 + z₀,
    3 * d₀ ^ 2 * k₀ - 3 * x₀ * z₀ * a₀ + 6 * x₀ * z₀ * d₀ + x₀ * y₀ * q₀ + 12 * x₀ * y₀ ^ 2
      + 3 * k₀ * a₀ - d₀ * q₀ - 9 * y₀ * a₀ + 3 * x₀ * z₀ + y₀,
    -(x₀ * z₀ * h₀) - x₀ ^ 2 * k₀ + k₀ * h₀ - 3 * y₀ * h₀ + 2 * x₀]

/-- The gadget minus what the wires carry is the explicit map of degree three. -/
theorem cubic10_eq (k : Fin 3) :
    rename Sum.inl (poly ℤ k) - bind₁ wire10 (carry10 k) = cubic10 k := by
  fin_cases k <;> simp [poly, wire10, carry10, cubic10, map_ofNat] <;> ring

theorem totalDegree_cubic10 (k : Fin 3) : (cubic10 k).totalDegree ≤ 3 := by
  fin_cases k <;> simp only [cubic10, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> exact le_trans (by td) (by norm_num)

theorem totalDegree_wire10 (w : Fin 7) : (wire10 w).totalDegree ≤ 3 := by
  fin_cases w <;> simp only [wire10, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;>
    exact le_trans (by td) (by norm_num)

/-- A wire is its own variable plus other things. -/
theorem pderiv_wire10_self (w : Fin 7) : pderiv (Sum.inr w) (wire10 w) = 1 := by
  fin_cases w <;> simp [wire10, pderiv_ofNat]

/-- A wire does not involve the variables of later wires. -/
theorem pderiv_wire10_of_lt (w w' : Fin 7) (h : w < w') : pderiv (Sum.inr w') (wire10 w) = 0 := by
  fin_cases w <;> fin_cases w' <;>
    first
      | exact absurd h (by decide)
      | simp [wire10, pderiv_ofNat]

theorem constantCoeff_carry10 (k : Fin 3) : constantCoeff (carry10 k) = 0 := by
  fin_cases k <;> simp [carry10]

end Template

section Lift

variable {K : Type*} [Field K]

/-- The values of the seven wire variables above a point `u = (x, y, z)`: the ones at which
every wire vanishes. -/
def lift10 (u : Fin 3 → K) : Fin 7 → K :=
  ![u 0 * u 1,
    u 0 * u 2 + 3 * u 1,
    -(u 0 ^ 2 * u 1 ^ 2),
    u 0 ^ 2,
    u 0 * u 1 * u 2 + 3 * u 1 ^ 2 + u 2,
    6 * u 0 ^ 2 * u 1 * u 2 + 18 * u 0 * u 1 ^ 2 + 6 * u 0 * u 2,
    3 * u 0 ^ 2 * u 1 ^ 2 * u 2 + 6 * u 0 * u 1 ^ 3 + 6 * u 0 * u 1 * u 2 + 7 * u 1 ^ 2]

theorem aeval_wire10_lift (u : Fin 3 → K) (w : Fin 7) :
    aeval (Sum.elim u (lift10 u)) (wire10 w) = 0 := by
  fin_cases w <;> simp [wire10, lift10] <;> ring

end Lift

/-- The ten-variable map of degree three: the wire extension of the gadget. -/
noncomputable def cubic10Map : V10 → MvPolynomial V10 ℤ := wireExt (poly ℤ) wire10 carry10

theorem cubic10Map_inl (k : Fin 3) : cubic10Map (Sum.inl k) = cubic10 k := cubic10_eq k

theorem cubic10Map_inr (w : Fin 7) : cubic10Map (Sum.inr w) = wire10 w := rfl

/-- Every coordinate of the ten-variable map has degree at most three. -/
theorem totalDegree_cubic10Map (a : V10) : (cubic10Map a).totalDegree ≤ 3 := by
  rcases a with k | w
  · rw [cubic10Map_inl]
    exact totalDegree_cubic10 k
  · exact totalDegree_wire10 w

/-- The Jacobian determinant of the ten-variable map is the constant `-2`. -/
theorem det_cubic10Map : (Matrix.of fun a b => pderiv b (cubic10Map a)).det = C (-2) := by
  have h := det_wireExt (poly ℤ) wire10 carry10 (fun w => (w : ℕ)) pderiv_wire10_self
    (fun c d hcd hle => pderiv_wire10_of_lt c d (lt_of_le_of_ne hle hcd))
  rw [cubic10Map, h]
  have := det_jacobian ℤ
  rw [jacobian] at this
  rw [this, rename_C]

/-- Above every point `u` the ten-variable map takes the value of the gadget, followed by
zeros. -/
theorem aeval_cubic10Map_lift {K : Type*} [Field K] (u : Fin 3 → K) (a : V10) :
    aeval (Sum.elim u (lift10 u)) (cubic10Map a) = Sum.elim (fun k => aeval u (poly ℤ k)) 0 a := by
  rcases a with k | w
  · rw [cubic10Map, aeval_wireExt_inl]
    have h0 : (fun c => aeval (Sum.elim u (lift10 u)) (wire10 c)) = (0 : Fin 7 → K) :=
      funext (aeval_wire10_lift u)
    rw [h0, aeval_zero, constantCoeff_carry10]
    simp
  · simpa [cubic10Map_inr] using aeval_wire10_lift u w

/-- The ten-variable map takes the same value at two points, over every field of
characteristic zero. -/
theorem cubic10Map_not_injective {K : Type*} [Field K] [CharZero K] :
    ¬ Function.Injective fun v : V10 → K => fun a => aeval v (cubic10Map a) := by
  intro hinj
  have h : Sum.elim (![0, 0, -1 / 4] : Fin 3 → K) (lift10 ![0, 0, -1 / 4])
      = Sum.elim (![1, -3 / 2, 13 / 2] : Fin 3 → K) (lift10 ![1, -3 / 2, 13 / 2]) := by
    apply hinj
    funext a
    beta_reduce
    rw [aeval_cubic10Map_lift, aeval_cubic10Map_lift]
    rcases a with k | w
    · fin_cases k <;> norm_num [poly]
    · rfl
  have h0 := congrFun h (Sum.inl 0)
  simp at h0

end KellerZero
