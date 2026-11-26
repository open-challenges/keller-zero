import KellerZero.Gadget
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The gadget is one cubic in disguise

Write `u = 1 + x y` and `w = 5 - 3 u - x² z`. Then

    R = x w,    x Q = 4 u + 2 - 3 u² w,    x² P = u² + u - u³ w,

so with `m = u w` the two quantities `Q R` and `P R²` depend on `m` and `w` only, and

    m³ - 2 m² + (Q R) m - 2 (P R²) = 0,        3 m² - 4 m + Q R = 2 w.

For a target `(a, b, c)` put `g(m) = m³ - 2 m² + b c m - 2 a c²`.

* `mem_fibre_iff_simple_root`: over every field of characteristic zero, when `c ≠ 0` the target
  is a value of the gadget exactly when `g` has a simple root in the field;
* `value_of_c_eq_zero`: a target with `c = 0` is always a value;
* `simple_root_or_triple`: over an algebraically closed field `g` has a simple root unless it is
  the cube `(m - 2/3)³`, which happens exactly on the curve of `omitted_curve`;
* `image_complex`, `image_real`: over the complex numbers and over the real numbers the values
  of the gadget are everything off that curve.

So the omitted curve is the locus where the cubic has a triple root.
-/

namespace KellerZero

variable {K : Type*} [Field K]

/-- The cubic of a target. -/
def cubic (a b c m : K) : K := m ^ 3 - 2 * m ^ 2 + b * c * m - 2 * a * c ^ 2

/-- The derivative of the cubic of a target. -/
def cubicDeriv (b c m : K) : K := 3 * m ^ 2 - 4 * m + b * c

theorem R_eq_mul (x y z : K) : R x y z = x * (5 - 3 * (1 + x * y) - x ^ 2 * z) := by
  simp only [R]; ring

theorem mul_Q_eq (x y z : K) :
    x * Q x y z = 4 * (1 + x * y) + 2
      - 3 * (1 + x * y) ^ 2 * (5 - 3 * (1 + x * y) - x ^ 2 * z) := by
  simp only [Q]; ring

theorem sq_mul_P_eq (x y z : K) :
    x ^ 2 * P x y z = (1 + x * y) ^ 2 + (1 + x * y)
      - (1 + x * y) ^ 3 * (5 - 3 * (1 + x * y) - x ^ 2 * z) := by
  simp only [P]; ring

/-- At every point, `m = u w` is a root of the cubic of the value. -/
theorem cubic_eq_zero (x y z : K) :
    cubic (P x y z) (Q x y z) (R x y z)
      ((1 + x * y) * (5 - 3 * (1 + x * y) - x ^ 2 * z)) = 0 := by
  simp only [cubic, P, Q, R]; ring

/-- At every point, the derivative of the cubic of the value at `m = u w` is `2 w`. -/
theorem cubicDeriv_eq (x y z : K) :
    cubicDeriv (Q x y z) (R x y z) ((1 + x * y) * (5 - 3 * (1 + x * y) - x ^ 2 * z))
      = 2 * (5 - 3 * (1 + x * y) - x ^ 2 * z) := by
  simp only [cubicDeriv, Q, R]; ring

/-- A target with `c = 0` is a value of the gadget. -/
theorem value_of_c_eq_zero (a b : K) :
    P 0 b (a - 4 * b ^ 2) = a ∧ Q 0 b (a - 4 * b ^ 2) = b ∧ R 0 b (a - 4 * b ^ 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [P, Q, R] <;> ring

/-- When `c ≠ 0`, the target `(a, b, c)` is a value of the gadget exactly when its cubic has a
simple root. -/
theorem mem_fibre_iff_simple_root [CharZero K] (a b c : K) (hc : c ≠ 0) :
    (∃ x y z : K, P x y z = a ∧ Q x y z = b ∧ R x y z = c) ↔
      ∃ m : K, cubic a b c m = 0 ∧ cubicDeriv b c m ≠ 0 := by
  constructor
  · rintro ⟨x, y, z, rfl, rfl, rfl⟩
    refine ⟨(1 + x * y) * (5 - 3 * (1 + x * y) - x ^ 2 * z), cubic_eq_zero x y z, ?_⟩
    rw [cubicDeriv_eq]
    rw [R_eq_mul] at hc
    exact mul_ne_zero two_ne_zero (right_ne_zero_of_mul hc)
  · rintro ⟨m, hm, hd⟩
    obtain ⟨w, hwdef⟩ : ∃ w : K, w = cubicDeriv b c m / 2 := ⟨_, rfl⟩
    have hw : w ≠ 0 := by rw [hwdef]; exact div_ne_zero hd two_ne_zero
    have h2w : 2 * w = 3 * m ^ 2 - 4 * m + b * c := by
      rw [hwdef, cubicDeriv]; ring
    clear hwdef hd
    have hx : c / w ≠ 0 := div_ne_zero hc hw
    refine ⟨c / w, (m / w - 1) / (c / w), (5 - 3 * (m / w) - w) / (c / w) ^ 2, ?_, ?_, ?_⟩
    all_goals
      have hu : 1 + c / w * ((m / w - 1) / (c / w)) = m / w := by field_simp; ring
      have hv : 5 - 3 * (1 + c / w * ((m / w - 1) / (c / w)))
          - (c / w) ^ 2 * ((5 - 3 * (m / w) - w) / (c / w) ^ 2) = w := by
        rw [hu]; field_simp; ring
    · have h := sq_mul_P_eq (c / w) ((m / w - 1) / (c / w)) ((5 - 3 * (m / w) - w) / (c / w) ^ 2)
      rw [hv, hu] at h
      have hx2 : (c / w) ^ 2 ≠ 0 := pow_ne_zero 2 hx
      apply mul_left_cancel₀ hx2
      rw [h]
      simp only [cubic] at hm
      field_simp
      linear_combination (1 / 2 : K) * hm + (m / 2) * h2w
    · have h := mul_Q_eq (c / w) ((m / w - 1) / (c / w)) ((5 - 3 * (m / w) - w) / (c / w) ^ 2)
      rw [hv, hu] at h
      apply mul_left_cancel₀ hx
      rw [h]
      field_simp
      linear_combination h2w
    · rw [R_eq_mul, hv]
      field_simp

/-- A root of the cubic that is not simple forces a second root `2 - 2 r`, which is simple
unless `r = 2/3`. -/
theorem simple_root_or_triple [CharZero K] (a b c r : K) (hr : cubic a b c r = 0) :
    (∃ m : K, cubic a b c m = 0 ∧ cubicDeriv b c m ≠ 0) ∨ (b * c = 4 / 3 ∧ a * c ^ 2 = 4 / 27) := by
  by_cases hd : cubicDeriv b c r = 0
  · by_cases h3 : 3 * r - 2 = 0
    · right
      have hr3 : r = 2 / 3 := by linear_combination h3 / 3
      subst hr3
      simp only [cubic, cubicDeriv] at hr hd
      constructor
      · linear_combination hd
      · linear_combination (-1 / 2 : K) * hr + (1 / 3 : K) * hd
    · left
      refine ⟨2 - 2 * r, ?_, ?_⟩
      · simp only [cubic, cubicDeriv] at hr hd ⊢
        linear_combination hr + (2 - 3 * r) * hd
      · simp only [cubic, cubicDeriv] at hr hd ⊢
        have : 3 * (2 - 2 * r) ^ 2 - 4 * (2 - 2 * r) + b * c = (3 * r - 2) ^ 2 := by
          linear_combination hd
        rw [this]
        exact pow_ne_zero 2 h3
  · exact Or.inl ⟨r, hr, hd⟩

/-- The triple-root locus is the omitted curve. -/
theorem on_curve_of_triple [CharZero K] (a b c : K) (h1 : b * c = 4 / 3)
    (h2 : a * c ^ 2 = 4 / 27) : b ≠ 0 ∧ a = b ^ 2 / 12 ∧ c = 4 / (3 * b) := by
  have hb : b ≠ 0 := by
    rintro rfl
    norm_num at h1
  have hc : c ≠ 0 := by
    rintro rfl
    norm_num at h1
  have hc' : c = 4 / (3 * b) := by
    field_simp
    linear_combination 3 * h1
  refine ⟨hb, ?_, hc'⟩
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  apply mul_right_cancel₀ hc2
  rw [h2, hc']
  field_simp
  norm_num

/-- If the cubic of a target has a root in the field, the target is a value of the gadget or
lies on the omitted curve. -/
theorem value_or_on_curve [CharZero K] (a b c r : K) (hr : cubic a b c r = 0) :
    (∃ x y z : K, P x y z = a ∧ Q x y z = b ∧ R x y z = c) ∨
      ∃ t : K, t ≠ 0 ∧ a = t ^ 2 / 12 ∧ b = t ∧ c = 4 / (3 * t) := by
  by_cases hc : c = 0
  · subst hc
    exact Or.inl ⟨0, b, a - 4 * b ^ 2, value_of_c_eq_zero a b⟩
  · rcases simple_root_or_triple a b c r hr with h | ⟨h1, h2⟩
    · exact Or.inl ((mem_fibre_iff_simple_root a b c hc).mpr h)
    · obtain ⟨hb, ha, hc'⟩ := on_curve_of_triple a b c h1 h2
      exact Or.inr ⟨b, hb, ha, rfl, hc'⟩

open Polynomial in
/-- The cubic of a target as a polynomial; it has degree three. -/
theorem exists_root_cubic_complex (a b c : ℂ) : ∃ r : ℂ, cubic a b c r = 0 := by
  have hdeg : (C (1 : ℂ) * X ^ 3 + C (-2) * X ^ 2 + C (b * c) * X + C (-2 * a * c ^ 2)).degree = 3 :=
    degree_cubic one_ne_zero
  obtain ⟨r, hr⟩ := Complex.exists_root (f := C (1 : ℂ) * X ^ 3 + C (-2) * X ^ 2 + C (b * c) * X
    + C (-2 * a * c ^ 2)) (by rw [hdeg]; norm_num)
  refine ⟨r, ?_⟩
  simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hr
  simp only [cubic]
  linear_combination hr

open Polynomial in
theorem exists_root_cubic_real (a b c : ℝ) : ∃ r : ℝ, cubic a b c r = 0 := by
  have hnat : (C (1 : ℝ) * X ^ 3 + C (-2) * X ^ 2 + C (b * c) * X
      + C (-2 * a * c ^ 2)).natDegree = 3 := natDegree_cubic one_ne_zero
  obtain ⟨r, hr⟩ := exists_root_of_odd_natDegree_irreducible_imp_natDegree_eq_one
    (R := ℝ) (fun {q} _ hodd hirr => by
      have h2 := hirr.natDegree_le_two
      rcases hodd with ⟨k, hk⟩
      omega)
    (C (1 : ℝ) * X ^ 3 + C (-2) * X ^ 2 + C (b * c) * X + C (-2 * a * c ^ 2))
    (by rw [hnat]; decide)
  refine ⟨r, ?_⟩
  simp only [IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hr
  simp only [cubic]
  linear_combination hr

/-- Over the complex numbers the values of the gadget are exactly the points off the curve. -/
theorem image_complex (a b c : ℂ) :
    (∃ x y z : ℂ, P x y z = a ∧ Q x y z = b ∧ R x y z = c) ↔
      ¬ ∃ t : ℂ, t ≠ 0 ∧ a = t ^ 2 / 12 ∧ b = t ∧ c = 4 / (3 * t) := by
  constructor
  · rintro ⟨x, y, z, hP, hQ, hR⟩ ⟨t, ht, ha, hb, hc⟩
    exact omitted_curve t ht x y z ⟨hP.trans ha, hQ.trans hb, hR.trans hc⟩
  · intro h
    obtain ⟨r, hr⟩ := exists_root_cubic_complex a b c
    exact (value_or_on_curve a b c r hr).resolve_right h

/-- Over the real numbers as well: a real cubic has a real root. -/
theorem image_real (a b c : ℝ) :
    (∃ x y z : ℝ, P x y z = a ∧ Q x y z = b ∧ R x y z = c) ↔
      ¬ ∃ t : ℝ, t ≠ 0 ∧ a = t ^ 2 / 12 ∧ b = t ∧ c = 4 / (3 * t) := by
  constructor
  · rintro ⟨x, y, z, hP, hQ, hR⟩ ⟨t, ht, ha, hb, hc⟩
    exact omitted_curve t ht x y z ⟨hP.trans ha, hQ.trans hb, hR.trans hc⟩
  · intro h
    obtain ⟨r, hr⟩ := exists_root_cubic_real a b c
    exact (value_or_on_curve a b c r hr).resolve_right h

end KellerZero
