import KellerZero.Gadget
import KellerZero.Wire
import KellerZero.Degree

/-!
# The gadget at degree three, in eleven variables

The eleven-variable map of degree three published on 20 July 2026 (gist `Spacerat/08b4a43f`,
"11 variable cubic jacobian conjecture counterexample"), written as a wire extension of the
gadget: variables `x, y, z` (`Sum.inl 0, 1, 2`) and eight wires `d, a, b, c, h, k, q, s`
(`Sum.inr 0 .. 7`).

* `cubic11_eq`: the wire extension is the explicit map `cubic11` (three coordinates) followed by
  the eight wires;
* `det_cubic11`: its Jacobian determinant is the constant `-2`;
* `totalDegree_cubic11`: every coordinate has degree at most three;
* `cubic11_not_injective`: it takes the same value at two points, over every field of
  characteristic zero.
-/

namespace KellerZero

open MvPolynomial

/-- The variables of the eleven-variable map. -/
abbrev V11 := Fin 3 ⊕ Fin 8

section Template

local notation "x₀" => (X (Sum.inl 0) : MvPolynomial V11 ℤ)
local notation "y₀" => (X (Sum.inl 1) : MvPolynomial V11 ℤ)
local notation "z₀" => (X (Sum.inl 2) : MvPolynomial V11 ℤ)
local notation "d₀" => (X (Sum.inr 0) : MvPolynomial V11 ℤ)
local notation "a₀" => (X (Sum.inr 1) : MvPolynomial V11 ℤ)
local notation "b₀" => (X (Sum.inr 2) : MvPolynomial V11 ℤ)
local notation "c₀" => (X (Sum.inr 3) : MvPolynomial V11 ℤ)
local notation "h₀" => (X (Sum.inr 4) : MvPolynomial V11 ℤ)
local notation "k₀" => (X (Sum.inr 5) : MvPolynomial V11 ℤ)
local notation "q₀" => (X (Sum.inr 6) : MvPolynomial V11 ℤ)
local notation "s₀" => (X (Sum.inr 7) : MvPolynomial V11 ℤ)

/-- The eight wires: each is its own variable plus a polynomial in `x, y, z` and earlier
wires. -/
noncomputable def wire₀ : Fin 8 → MvPolynomial V11 ℤ :=
  ![d₀ - x₀ * y₀,
    a₀ - d₀ ^ 2 + 2 * d₀ * x₀ * y₀,
    b₀ + 3 * x₀ ^ 2 * y₀,
    c₀ + x₀ * y₀ * z₀ + 3 * y₀ ^ 2 + 2 * z₀,
    h₀ - x₀ ^ 2,
    k₀ + x₀ * z₀,
    q₀ + b₀ * z₀ + 3 * c₀ * x₀,
    s₀ + a₀ * z₀ + c₀ * x₀ * y₀ - x₀ * y₀ * z₀ - 7 * y₀ ^ 2 + c₀ * d₀ - d₀ * z₀]

/-- What the wires carry away from the three coordinates of the gadget. -/
noncomputable def carry₀ : Fin 3 → MvPolynomial (Fin 8) ℤ :=
  ![X 1 * X 3 + X 3 * X 0 ^ 2 + X 0 * X 7, X 2 * X 3 + X 0 * X 6, X 4 * X 5]

/-- The first three coordinates of the eleven-variable map. -/
noncomputable def cubic11 : Fin 3 → MvPolynomial V11 ℤ :=
  ![-(a₀ * c₀) - a₀ * d₀ * z₀ - 3 * a₀ * y₀ ^ 2 - 2 * a₀ * z₀ - c₀ * d₀ ^ 2 + d₀ ^ 2 * z₀
      - d₀ * s₀ + 7 * d₀ * y₀ ^ 2 + s₀ * x₀ * y₀ + 3 * x₀ * y₀ * z₀ + 4 * y₀ ^ 2 + z₀,
    -(b₀ * c₀) - b₀ * d₀ * z₀ - 3 * b₀ * y₀ ^ 2 - 2 * b₀ * z₀ - 3 * c₀ * d₀ * x₀ - d₀ * q₀
      + q₀ * x₀ * y₀ + 12 * x₀ * y₀ ^ 2 + 3 * x₀ * z₀ + y₀,
    -(h₀ * k₀) - h₀ * x₀ * z₀ + k₀ * x₀ ^ 2 - 3 * x₀ ^ 2 * y₀ + 2 * x₀]

/-- The gadget minus what the wires carry is the explicit map of degree three. -/
theorem cubic11_eq (k : Fin 3) :
    rename Sum.inl (poly ℤ k) - bind₁ wire₀ (carry₀ k) = cubic11 k := by
  fin_cases k <;> simp [poly, wire₀, carry₀, cubic11, map_ofNat] <;> ring

theorem totalDegree_cubic11 (k : Fin 3) : (cubic11 k).totalDegree ≤ 3 := by
  fin_cases k <;> simp only [cubic11, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> exact le_trans (by td) (by norm_num)

theorem totalDegree_wire₀ (w : Fin 8) : (wire₀ w).totalDegree ≤ 3 := by
  fin_cases w <;> simp only [wire₀, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;>
    exact le_trans (by td) (by norm_num)

/-- A wire is its own variable plus other things. -/
theorem pderiv_wire₀_self (w : Fin 8) : pderiv (Sum.inr w) (wire₀ w) = 1 := by
  fin_cases w <;> simp [wire₀, pderiv_ofNat]

/-- A wire does not involve the variables of later wires. -/
theorem pderiv_wire₀_of_lt (w w' : Fin 8) (h : w < w') : pderiv (Sum.inr w') (wire₀ w) = 0 := by
  fin_cases w <;> fin_cases w' <;>
    first
      | exact absurd h (by decide)
      | simp [wire₀, pderiv_ofNat]

theorem constantCoeff_carry₀ (k : Fin 3) : constantCoeff (carry₀ k) = 0 := by
  fin_cases k <;> simp [carry₀]

end Template

section Lift

variable {K : Type*} [Field K]

/-- The values of the eight wire variables above a point `u = (x, y, z)`: the ones at which every
wire vanishes. -/
def lift₀ (u : Fin 3 → K) : Fin 8 → K :=
  ![u 0 * u 1,
    -(u 0 ^ 2 * u 1 ^ 2),
    -(3 * u 0 ^ 2 * u 1),
    -(u 0 * u 1 * u 2 + 3 * u 1 ^ 2 + 2 * u 2),
    u 0 ^ 2,
    -(u 0 * u 2),
    6 * u 0 ^ 2 * u 1 * u 2 + 9 * u 0 * u 1 ^ 2 + 6 * u 0 * u 2,
    3 * u 0 ^ 2 * u 1 ^ 2 * u 2 + 6 * u 0 * u 1 ^ 3 + 6 * u 0 * u 1 * u 2 + 7 * u 1 ^ 2]

theorem aeval_wire₀_lift (u : Fin 3 → K) (w : Fin 8) :
    aeval (Sum.elim u (lift₀ u)) (wire₀ w) = 0 := by
  fin_cases w <;> simp [wire₀, lift₀] <;> ring

end Lift

/-- The eleven-variable map of degree three: the wire extension of the gadget. -/
noncomputable def cubic11Map : V11 → MvPolynomial V11 ℤ := wireExt (poly ℤ) wire₀ carry₀

theorem cubic11Map_inl (k : Fin 3) : cubic11Map (Sum.inl k) = cubic11 k := cubic11_eq k

theorem cubic11Map_inr (w : Fin 8) : cubic11Map (Sum.inr w) = wire₀ w := rfl

/-- Every coordinate of the eleven-variable map has degree at most three. -/
theorem totalDegree_cubic11Map (a : V11) : (cubic11Map a).totalDegree ≤ 3 := by
  rcases a with k | w
  · rw [cubic11Map_inl]
    exact totalDegree_cubic11 k
  · exact totalDegree_wire₀ w

/-- The Jacobian determinant of the eleven-variable map is the constant `-2`. -/
theorem det_cubic11Map : (Matrix.of fun a b => pderiv b (cubic11Map a)).det = C (-2) := by
  have h := det_wireExt (poly ℤ) wire₀ carry₀ (fun w => (w : ℕ)) pderiv_wire₀_self
    (fun c d hcd hle => pderiv_wire₀_of_lt c d (lt_of_le_of_ne hle hcd))
  rw [cubic11Map, h]
  have := det_jacobian ℤ
  rw [jacobian] at this
  rw [this, rename_C]

/-- Above every point `u` the eleven-variable map takes the value of the gadget, followed by
zeros. -/
theorem aeval_cubic11Map_lift {K : Type*} [Field K] (u : Fin 3 → K) (a : V11) :
    aeval (Sum.elim u (lift₀ u)) (cubic11Map a) = Sum.elim (fun k => aeval u (poly ℤ k)) 0 a := by
  rcases a with k | w
  · rw [cubic11Map, aeval_wireExt_inl]
    have h0 : (fun c => aeval (Sum.elim u (lift₀ u)) (wire₀ c)) = (0 : Fin 8 → K) :=
      funext (aeval_wire₀_lift u)
    rw [h0, aeval_zero, constantCoeff_carry₀]
    simp
  · simpa [cubic11Map_inr] using aeval_wire₀_lift u w

/-- The eleven-variable map takes the same value at two points, over every field of
characteristic zero. -/
theorem cubic11Map_not_injective {K : Type*} [Field K] [CharZero K] :
    ¬ Function.Injective fun v : V11 → K => fun a => aeval v (cubic11Map a) := by
  intro hinj
  have h : Sum.elim (![0, 0, -1 / 4] : Fin 3 → K) (lift₀ ![0, 0, -1 / 4])
      = Sum.elim (![1, -3 / 2, 13 / 2] : Fin 3 → K) (lift₀ ![1, -3 / 2, 13 / 2]) := by
    apply hinj
    funext a
    beta_reduce
    rw [aeval_cubic11Map_lift, aeval_cubic11Map_lift]
    rcases a with k | w
    · fin_cases k <;> norm_num [poly]
    · rfl
  have h0 := congrFun h (Sum.inl 0)
  simp at h0

end KellerZero
