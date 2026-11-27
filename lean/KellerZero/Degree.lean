import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# Bounding the total degree of an explicit polynomial

Small lemmas of the shape "if the parts have degree at most `a` and `b`, the whole has degree at
most ...", and the tactic `td` that applies them down to the variables and constants. The goal
`p.totalDegree ≤ 3` is then proved as `le_trans (by td) (by norm_num)`.
-/

namespace KellerZero.Deg

open MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} {p q : MvPolynomial σ R} {a b : ℕ}

theorem var [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 :=
  (totalDegree_X i).le

theorem const (c : R) : (C c : MvPolynomial σ R).totalDegree ≤ 0 := (totalDegree_C c).le

theorem one : (1 : MvPolynomial σ R).totalDegree ≤ 0 := totalDegree_one.le

theorem zero : (0 : MvPolynomial σ R).totalDegree ≤ 0 := totalDegree_zero.le

theorem ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : MvPolynomial σ R).totalDegree ≤ 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact (totalDegree_C _).le

theorem add (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p + q).totalDegree ≤ max a b :=
  (totalDegree_add p q).trans (max_le_max hp hq)

theorem sub (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p - q).totalDegree ≤ max a b :=
  (totalDegree_sub p q).trans (max_le_max hp hq)

theorem mul (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)

theorem pow (n : ℕ) (hp : p.totalDegree ≤ a) : (p ^ n).totalDegree ≤ n * a :=
  (totalDegree_pow p n).trans (Nat.mul_le_mul_left n hp)

theorem neg (hp : p.totalDegree ≤ a) : (-p).totalDegree ≤ a := by
  rw [totalDegree_neg]
  exact hp

theorem rename {τ : Type*} (f : σ → τ) (hp : p.totalDegree ≤ a) :
    (MvPolynomial.rename f p).totalDegree ≤ a :=
  (totalDegree_rename_le f p).trans hp

theorem vec7248 (k : Fin 3) : ((![7, 24, 8] : Fin 3 → MvPolynomial σ R) k).totalDegree ≤ 0 := by
  fin_cases k
  · exact ofNat 7
  · exact ofNat 24
  · exact ofNat 8

theorem vec300 (k : Fin 3) : ((![3, 0, 0] : Fin 3 → MvPolynomial σ R) k).totalDegree ≤ 0 := by
  fin_cases k
  · exact ofNat 3
  · exact totalDegree_zero.le
  · exact totalDegree_zero.le

end KellerZero.Deg

/-- Bound the total degree of a polynomial written with variables, constants, `+`, `-`, `*` and
powers, and with renamed polynomials whose degree bound is a hypothesis. Leaves a bound with
unknowns filled in; close the numeric side with `norm_num`. -/
macro "td" : tactic =>
  `(tactic| repeat' with_reducible first
    | exact KellerZero.Deg.var _
    | exact KellerZero.Deg.const _
    | exact KellerZero.Deg.one
    | exact KellerZero.Deg.zero
    | exact KellerZero.Deg.ofNat _
    | assumption
    | exact KellerZero.Deg.rename _ (by assumption)
    | apply KellerZero.Deg.add
    | apply KellerZero.Deg.sub
    | apply KellerZero.Deg.mul
    | apply KellerZero.Deg.neg
    | apply KellerZero.Deg.pow)
