import KellerZero.Gadget

/-!
# The gadget at degree three

`cubicPoly` is a polynomial map in twelve variables, every coordinate of degree at most three,
obtained from the gadget by the reduction of Bass, Connell and Wright (the construction is
`scripts/lower_degree.py`). Variables `0, 1, 2` are `x, y, z`; variables `3` to `11` are new.

* `cubic_fibre`: over every field, a target `(a, b, c, 0, ..., 0)` is a value of `cubicPoly`
  exactly when `(a, b, c)` is a value of the gadget;
* `cubicPoly_not_injective`: so it takes the same value at two points.

That its Jacobian determinant is the constant `-2` is checked by exact arithmetic
(`scripts/check_gadget.py submissions/SecurityQQ/gadget.json`), and in Lean it is the open
statement `KellerZero.Open.CubicGadgetIsKeller`.
-/

namespace KellerZero

open MvPolynomial

/-- The gadget at degree three, in twelve variables, over any commutative ring. -/
noncomputable def cubicPoly (A : Type*) [CommRing A] : Fin 12 → MvPolynomial (Fin 12) A :=
  ![X 2 - X 5 * X 7 + X 3 * X 9 + X 3 * X 8 - 2 * X 3 * X 5 - X 2 * X 7 - 2 * X 2 * X 3 + 4 * X 1 ^ 2 - X 3 ^ 2 * X 5 + X 2 * X 3 * X 7 + 2 * X 2 * X 3 ^ 2 - 3 * X 1 ^ 2 * X 7 - 7 * X 1 ^ 2 * X 3 + X 0 * X 1 * X 9 + X 0 * X 1 * X 8 - 2 * X 0 * X 1 * X 5 + X 0 * X 1 * X 2,
    X 1 - 3 * X 4 * X 5 + X 3 * X 6 - 3 * X 2 * X 4 - 3 * X 0 * X 5 + 3 * X 2 * X 3 * X 4 - 9 * X 1 ^ 2 * X 4 + 3 * X 0 * X 3 * X 5 + X 0 * X 1 * X 6 + 3 * X 0 * X 1 ^ 2,
    2 * X 0 + X 10 * X 11 + X 0 * X 2 * X 10 + X 0 ^ 2 * X 11 - 3 * X 0 ^ 2 * X 1,
    X 3 + X 0 * X 1,
    X 4 + X 0 + X 0 ^ 2 * X 1,
    X 5 + X 2 + 3 * X 1 ^ 2 + X 0 * X 1 * X 2,
    X 6 + 3 * X 2 * X 4 + 3 * X 0 * X 5,
    X 7 - X 3 ^ 2 - 2 * X 0 * X 1 * X 3,
    X 8 + X 0 * X 1 * X 5,
    X 9 - X 3 * X 5 + X 2 * X 7 + 2 * X 2 * X 3 - X 1 ^ 2,
    X 10 + X 0 ^ 2,
    X 11 + X 0 * X 2]

variable {K : Type*} [Field K]

/-- The values of the new variables above a point `(x, y, z)`. -/
def cubicLift (x y z : K) : Fin 12 → K :=
  ![x, y, z, -(x * y), -(x + x ^ 2 * y), -(z + 3 * y ^ 2 + x * y * z),
    3 * z * (x + x ^ 2 * y) + 3 * x * (z + 3 * y ^ 2 + x * y * z),
    -(x * y) ^ 2,
    x * y * (z + 3 * y ^ 2 + x * y * z),
    x * y * (z + 3 * y ^ 2 + x * y * z) + z * (x * y) ^ 2 + 2 * z * (x * y) + y ^ 2,
    -x ^ 2, -(x * z)]

/-- Above every point, the degree-three map takes the value of the gadget, followed by zeros. -/
theorem eval_cubicLift (x y z : K) :
    (fun i => eval (cubicLift x y z) (cubicPoly K i))
      = ![P x y z, Q x y z, R x y z, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [cubicPoly, cubicLift, P, Q, R] <;> ring

/-- A target `(a, b, c, 0, ..., 0)` is a value of the degree-three map exactly when `(a, b, c)`
is a value of the gadget. -/
theorem cubic_fibre (a b c : K) :
    (∃ p : Fin 12 → K,
        (fun i => eval p (cubicPoly K i)) = ![a, b, c, 0, 0, 0, 0, 0, 0, 0, 0, 0]) ↔
      ∃ x y z : K, P x y z = a ∧ Q x y z = b ∧ R x y z = c := by
  constructor
  · rintro ⟨p, hp⟩
    have h0 := congrFun hp 0
    have h1 := congrFun hp 1
    have h2 := congrFun hp 2
    have h3 := congrFun hp 3
    have h4 := congrFun hp 4
    have h5 := congrFun hp 5
    have h6 := congrFun hp 6
    have h7 := congrFun hp 7
    have h8 := congrFun hp 8
    have h9 := congrFun hp 9
    have h10 := congrFun hp 10
    have h11 := congrFun hp 11
    simp [cubicPoly] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    generalize p 0 = x at *
    generalize p 1 = y at *
    generalize p 2 = z at *
    generalize p 3 = t1 at *
    generalize p 4 = t2 at *
    generalize p 5 = t3 at *
    generalize p 6 = t4 at *
    generalize p 7 = t5 at *
    generalize p 8 = t6 at *
    generalize p 9 = t7 at *
    generalize p 10 = t8 at *
    generalize p 11 = t9 at *
    have e1 : t1 = -(x * y) := by linear_combination h3
    subst e1
    have e2 : t2 = -(x + x ^ 2 * y) := by linear_combination h4
    subst e2
    have e3 : t3 = -(z + 3 * y ^ 2 + x * y * z) := by linear_combination h5
    subst e3
    have e4 : t4 = 3 * z * (x + x ^ 2 * y) + 3 * x * (z + 3 * y ^ 2 + x * y * z) := by
      linear_combination h6
    subst e4
    have e5 : t5 = -(x * y) ^ 2 := by linear_combination h7
    subst e5
    have e6 : t6 = x * y * (z + 3 * y ^ 2 + x * y * z) := by linear_combination h8
    subst e6
    have e7 : t7 = x * y * (z + 3 * y ^ 2 + x * y * z) + z * (x * y) ^ 2 + 2 * z * (x * y) + y ^ 2 := by
      linear_combination h9
    subst e7
    have e8 : t8 = -x ^ 2 := by linear_combination h10
    subst e8
    have e9 : t9 = -(x * z) := by linear_combination h11
    subst e9
    refine ⟨x, y, z, ?_, ?_, ?_⟩
    · simp only [P]; linear_combination h0
    · simp only [Q]; linear_combination h1
    · simp only [R]; linear_combination h2
  · rintro ⟨x, y, z, rfl, rfl, rfl⟩
    exact ⟨cubicLift x y z, eval_cubicLift x y z⟩

/-- The degree-three map is not injective, over every field of characteristic zero. -/
theorem cubicPoly_not_injective [CharZero K] :
    ¬ Function.Injective fun p : Fin 12 → K => fun i => eval p (cubicPoly K i) := by
  intro hinj
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, -⟩ := three_points (K := K)
  have h : cubicLift (0 : K) 0 (-1 / 4) = cubicLift 1 (-3 / 2) (13 / 2) := by
    apply hinj
    show (fun i => eval (cubicLift (0 : K) 0 (-1 / 4)) (cubicPoly K i))
      = fun i => eval (cubicLift (1 : K) (-3 / 2) (13 / 2)) (cubicPoly K i)
    rw [eval_cubicLift, eval_cubicLift, a1, a2, a3, b1, b2, b3]
  have h0 := congrFun h 0
  simp [cubicLift] at h0

end KellerZero
