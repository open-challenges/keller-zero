import KellerZero.Cubic10
import KellerZero.Reduction
import KellerZero.Proofs.ReductionMapIsKeller

/-!
# The reduction at degree three

`cubicReduction φ` is a wire extension of the map `reductionMap φ` of Stambler's reduction:
seven wires for every block (the ten-variable gadget of `Cubic10`) and three more for every
clause, which carry the product of its three literal values. `10 n + 13 m` variables in all.

* `totalDegree_cubicReduction`: every coordinate has degree at most three;
* `det_cubicReduction`: the Jacobian determinant is the constant `(-3456) ^ (n + m)`;
* `exists_zero_cubicReduction_iff_satisfiable`: over every field of characteristic zero the map
  has a zero exactly when the formula is satisfiable.

A map of degree two with constant nonzero Jacobian determinant is injective
(`Proofs.QuadraticKellerMapsAreInjective`), and in fact bijective (Wang, 1980), so three is the
least degree at which the question "is there a zero?" can be hard.
-/

namespace KellerZero

open MvPolynomial

variable {n m : ℕ}

/-- The wires of the reduction: seven for every block, three for every clause. -/
abbrev Wire (n m : ℕ) := (Fin n ⊕ Fin m) × Fin 7 ⊕ Fin m × Fin 3

/-- The variables of the reduction at degree three. -/
abbrev Var3 (n m : ℕ) := Var n m ⊕ Wire n m

theorem card_var3 (n m : ℕ) : Fintype.card (Var3 n m) = 10 * n + 13 * m := by
  simp [Var3, Var, Wire]
  ring

/-- The variables of the ten-variable gadget, placed in block `b`. -/
def emb (b : Fin n ⊕ Fin m) : V10 → Var3 n m :=
  Sum.elim (fun j => Sum.inl (b, j)) (fun w => Sum.inr (Sum.inl (b, w)))

theorem emb_injective (b : Fin n ⊕ Fin m) : Function.Injective (emb b) := by
  rintro (i | i) (j | j) h <;> simp [emb] at h <;> simp [h]

/-- The derivative of a polynomial of block `b` in a variable outside the block is zero. -/
theorem pderiv_rename_emb (b : Fin n ⊕ Fin m) (v : Var3 n m) (hv : ∀ a, emb b a ≠ v)
    (p : MvPolynomial V10 ℤ) : pderiv v (rename (emb b) p) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  have := (vars_rename _ _) h
  simp only [Finset.mem_image] at this
  obtain ⟨a, -, ha⟩ := this
  exact hv a ha

/-- The sign of a literal: `1` for a variable, `-1` for a negated variable. -/
def Literal.sign (l : Literal n) : ℤ := if l.positive then 1 else -1

/-- `1` for a variable, `0` for a negated variable. -/
def Literal.const (l : Literal n) : ℤ := if l.positive then 1 else 0

/-- The polynomial that is `1` when the literal is false and `0` when it is true:
`1 - x ^ 2` for a variable and `x ^ 2` for a negated one. -/
noncomputable def falsity (l : Literal n) : MvPolynomial (Var3 n m) ℤ :=
  C l.const - C l.sign * X (Sum.inl (Sum.inl l.var, 0)) ^ 2

/-- The wire variable of the block of the literal's variable that stands for `x ^ 2`. -/
noncomputable def sq (l : Literal n) : MvPolynomial (Var3 n m) ℤ :=
  X (Sum.inr (Sum.inl (Sum.inl l.var, 3)))

theorem one_sub_rename_literalPoly (l : Literal n) :
    1 - rename Sum.inl (literalPoly (m := m) l) = (falsity l : MvPolynomial (Var3 n m) ℤ) := by
  unfold literalPoly falsity Literal.const Literal.sign
  split_ifs <;> simp

/-- The wires. Those of a block are the wires of the ten-variable gadget in the variables of
the block. Those of a clause are their own variable plus products of at most three variables
of the blocks of its literals. -/
noncomputable def wire (φ : Fin m → Clause n) : Wire n m → MvPolynomial (Var3 n m) ℤ
  | Sum.inl (b, w) => rename (emb b) (wire10 w)
  | Sum.inr (j, i) =>
    X (Sum.inr (Sum.inr (j, i))) + (![
      -(C (φ j 0).sign * sq (φ j 0) * falsity (φ j 1) + C (φ j 1).sign * sq (φ j 1) * falsity (φ j 0)
          + C (φ j 0).sign * C (φ j 1).sign * sq (φ j 0) * sq (φ j 1)),
      C (φ j 2).sign * sq (φ j 2) * falsity (φ j 0),
      C (φ j 1).sign * C (φ j 2).sign * sq (φ j 1) * sq (φ j 2)] :
        Fin 3 → MvPolynomial (Var3 n m) ℤ) i

/-- The falsity polynomial of a literal, as a polynomial in the wires. -/
noncomputable def falsityS (l : Literal n) : MvPolynomial (Wire n m) ℤ :=
  C l.const + C l.sign * X (Sum.inl (Sum.inl l.var, 3))

/-- The product of the three falsity polynomials of a clause, through the three wires of the
clause. -/
noncomputable def prodS (c : Clause n) (j : Fin m) : MvPolynomial (Wire n m) ℤ :=
  (X (Sum.inr (j, 0)) + falsityS (c 0) * falsityS (c 1)) * falsityS (c 2)
    - X (Sum.inr (j, 1)) * falsityS (c 1) + X (Sum.inr (j, 2)) * falsityS (c 0)

/-- What the wires carry away from each coordinate of the map of the reduction. -/
noncomputable def carry (φ : Fin m → Clause n) : Var n m → MvPolynomial (Wire n m) ℤ
  | (Sum.inl i, k) => 12 * rename (fun w => Sum.inl (Sum.inl i, w)) (carry10 k)
  | (Sum.inr j, k) => 12 * rename (fun w => Sum.inl (Sum.inr j, w)) (carry10 k)
      - (![7, 24, 8] : Fin 3 → MvPolynomial (Wire n m) ℤ) k
        * (prodS (φ j) j - C ((φ j 0).const * (φ j 1).const * (φ j 2).const))

/-- The map of the reduction at degree three. -/
noncomputable def cubicReduction (φ : Fin m → Clause n) : Var3 n m → MvPolynomial (Var3 n m) ℤ :=
  wireExt (reductionMap φ) (wire φ) (carry φ)

/-! ## The Jacobian determinant -/

/-- The rank of a wire: a wire involves only wires of lower rank. -/
def wireRank : Wire n m → ℕ
  | Sum.inl (_, w) => w
  | Sum.inr _ => 7

theorem pderiv_wire_self (φ : Fin m → Clause n) (c : Wire n m) :
    pderiv (Sum.inr c) (wire φ c) = 1 := by
  rcases c with ⟨b, w⟩ | ⟨j, i⟩
  · have h := pderiv_rename (R := ℤ) (emb_injective (n := n) (m := m) b) (Sum.inr w) (wire10 w)
    rw [pderiv_wire10_self, map_one] at h
    exact h
  · fin_cases i <;> simp [wire, sq, falsity]

theorem pderiv_wire_of_ne (φ : Fin m → Clause n) (c d : Wire n m) (hcd : c ≠ d)
    (hr : wireRank c ≤ wireRank d) : pderiv (Sum.inr d) (wire φ c) = 0 := by
  rcases c with ⟨b, w⟩ | ⟨j, i⟩
  · rcases d with ⟨b', w'⟩ | ⟨j', i'⟩
    · by_cases hb : b' = b
      · subst hb
        have hlt : w < w' := by
          have hle : w ≤ w' := hr
          exact lt_of_le_of_ne hle (fun h => hcd (by rw [h]))
        have h := pderiv_rename (R := ℤ) (emb_injective (n := n) (m := m) b') (Sum.inr w') (wire10 w)
        rw [pderiv_wire10_of_lt w w' hlt, map_zero] at h
        exact h
      · exact pderiv_rename_emb b _ (by rintro (a | a) h <;> simp [emb] at h; exact hb h.1.symm) _
    · exact pderiv_rename_emb b _ (by rintro (a | a) h <;> simp [emb] at h) _
  · rcases d with ⟨b', w'⟩ | ⟨j', i'⟩
    · exfalso
      have h8 : (7 : ℕ) ≤ (w' : ℕ) := hr
      omega
    · have hne : ¬ (j = j' ∧ i = i') := fun h => hcd (by rw [h.1, h.2])
      fin_cases i <;> simp [wire, sq, falsity, Pi.single_apply] <;>
        intro h1 h2 <;> exact hne ⟨h1, h2⟩

/-- The Jacobian determinant of the map of the reduction at degree three. -/
theorem det_cubicReduction (φ : Fin m → Clause n) :
    (Matrix.of fun a b => pderiv b (cubicReduction φ a)).det = C ((-3456) ^ (n + m)) := by
  rw [cubicReduction, det_wireExt (reductionMap φ) (wire φ) (carry φ) wireRank
    (pderiv_wire_self φ) (pderiv_wire_of_ne φ), Proofs.ReductionMapIsKeller n m φ, rename_C]

/-! ## The zeros -/

theorem constantCoeff_carry (φ : Fin m → Clause n) (a : Var n m) :
    constantCoeff (carry φ a) = 0 := by
  obtain ⟨b | b, k⟩ := a
  · simp [carry, constantCoeff_rename, constantCoeff_carry10]
  · simp [carry, constantCoeff_rename, constantCoeff_carry10, prodS, falsityS]

section Zeros

variable {K : Type*} [Field K]

/-- The values of the wire variables above a point of the map of the reduction. -/
def wireValues (φ : Fin m → Clause n) (u : Var n m → K) : Wire n m → K
  | Sum.inl (b, w) => lift10 (fun j => u (b, j)) w
  | Sum.inr (j, i) =>
    (![((φ j 0).sign : K) * u (Sum.inl (φ j 0).var, 0) ^ 2
          * ((φ j 1).const - (φ j 1).sign * u (Sum.inl (φ j 1).var, 0) ^ 2)
        + ((φ j 1).sign : K) * u (Sum.inl (φ j 1).var, 0) ^ 2
          * ((φ j 0).const - (φ j 0).sign * u (Sum.inl (φ j 0).var, 0) ^ 2)
        + ((φ j 0).sign : K) * (φ j 1).sign * u (Sum.inl (φ j 0).var, 0) ^ 2
          * u (Sum.inl (φ j 1).var, 0) ^ 2,
      -(((φ j 2).sign : K) * u (Sum.inl (φ j 2).var, 0) ^ 2
          * ((φ j 0).const - (φ j 0).sign * u (Sum.inl (φ j 0).var, 0) ^ 2)),
      -(((φ j 1).sign : K) * (φ j 2).sign * u (Sum.inl (φ j 1).var, 0) ^ 2
          * u (Sum.inl (φ j 2).var, 0) ^ 2)] : Fin 3 → K) i

theorem aeval_wire_wireValues (φ : Fin m → Clause n) (u : Var n m → K) (c : Wire n m) :
    aeval (Sum.elim u (wireValues φ u)) (wire φ c) = 0 := by
  rcases c with ⟨b, w⟩ | ⟨j, i⟩
  · have hcomp : (Sum.elim u (wireValues φ u)) ∘ emb b
        = Sum.elim (fun j => u (b, j)) (lift10 fun j => u (b, j)) := by
      funext a
      rcases a with a | a <;> simp [emb, wireValues]
    simp only [wire, aeval_rename, hcomp]
    exact aeval_wire10_lift _ w
  · fin_cases i <;> simp [wire, sq, falsity, wireValues, lift10]

/-- At degree three as at degree seven: the map has a zero exactly when the formula is
satisfiable. -/
theorem exists_zero_cubicReduction_iff_satisfiable [CharZero K] (φ : Fin m → Clause n) :
    (∃ v : Var3 n m → K, ∀ a, aeval v (cubicReduction φ a) = 0) ↔
      ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ := by
  rw [← exists_zero_reductionMap_iff_satisfiable (K := K) φ]
  constructor
  · rintro ⟨v, hv⟩
    have hsplit : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := (Sum.elim_comp_inl_inr v).symm
    rw [hsplit] at hv
    exact ⟨v ∘ Sum.inl, ((aeval_wireExt_eq_zero_iff (reductionMap φ) (wire φ) (carry φ)
      (constantCoeff_carry φ) _ _).mp hv).1⟩
  · rintro ⟨u, hu⟩
    exact ⟨Sum.elim u (wireValues φ u), (aeval_wireExt_eq_zero_iff (reductionMap φ) (wire φ)
      (carry φ) (constantCoeff_carry φ) _ _).mpr ⟨hu, aeval_wire_wireValues φ u⟩⟩

end Zeros

/-! ## The degree -/

/-- What is left of the product of the three falsity polynomials of a clause once the wires
have carried the product itself away: a polynomial of degree three. -/
noncomputable def remainder (c : Clause n) (j : Fin m) : MvPolynomial (Var3 n m) ℤ :=
  X (Sum.inr (Sum.inr (j, 0))) * falsity (c 2)
    + C (c 2).sign * X (Sum.inr (Sum.inr (j, 0))) * sq (c 2)
    - X (Sum.inr (Sum.inr (j, 1))) * falsity (c 1)
    - C (c 1).sign * X (Sum.inr (Sum.inr (j, 1))) * sq (c 1)
    + X (Sum.inr (Sum.inr (j, 2))) * falsity (c 0)
    + C (c 0).sign * X (Sum.inr (Sum.inr (j, 2))) * sq (c 0)
    + C (c 0).sign * C (c 1).sign * C (c 2).sign * sq (c 0) * sq (c 1) * sq (c 2)

/-- The gadget of a block minus what its seven wires carry is the ten-variable gadget in the
variables of the block. -/
theorem block_eq (φ : Fin m → Clause n) (b : Fin n ⊕ Fin m) (k : Fin 3) :
    rename Sum.inl (gadgetAt b k)
        - 12 * bind₁ (wire φ) (rename (fun w => Sum.inl (b, w)) (carry10 k))
      = 12 * rename (emb b) (cubic10 k) + (![3, 0, 0] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k := by
  have h1 : rename (Sum.inl : Var n m → Var3 n m) (rename (fun j => ((b, j) : Var n m)) (poly ℤ k))
      = rename (emb b) (rename Sum.inl (poly ℤ k)) := by
    rw [rename_rename, rename_rename]
    rfl
  have h2 : bind₁ (wire φ) (rename (fun w => Sum.inl (b, w)) (carry10 k))
      = rename (emb b) (bind₁ wire10 (carry10 k)) := by
    rw [bind₁_rename, rename_bind₁]
    rfl
  have h3 : rename (Sum.inl : Var n m → Var3 n m) ((![3, 0, 0] : Fin 3 → MvPolynomial (Var n m) ℤ) k)
      = (![3, 0, 0] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k := by
    fin_cases k <;> simp [map_ofNat]
  rw [gadgetAt, map_add, map_mul, map_ofNat, h1, h2, h3, ← cubic10_eq k, map_sub]
  ring

/-- The product of the three falsity polynomials, through the wires. -/
theorem bind₁_prodS (φ : Fin m → Clause n) (j : Fin m) :
    bind₁ (wire φ) (prodS (φ j) j)
      = falsity (φ j 0) * falsity (φ j 1) * falsity (φ j 2) + remainder (φ j) j := by
  simp [prodS, falsityS, wire, wire10, emb, remainder, sq, falsity]
  ring

theorem one_sub_rename_clausePoly (c : Clause n) :
    1 - rename (Sum.inl : Var n m → Var3 n m) (clausePoly c)
      = falsity (c 0) * falsity (c 1) * falsity (c 2) := by
  simp only [clausePoly, map_sub, map_one, map_mul, Fin.prod_univ_three, sub_sub_cancel,
    one_sub_rename_literalPoly]

/-- A coordinate of a variable block, written out. -/
theorem cubicReduction_inl_inl (φ : Fin m → Clause n) (i : Fin n) (k : Fin 3) :
    cubicReduction φ (Sum.inl (Sum.inl i, k))
      = 12 * rename (emb (Sum.inl i)) (cubic10 k)
        + (![3, 0, 0] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k := by
  rw [← block_eq φ (Sum.inl i) k]
  simp [cubicReduction, wireExt, reductionMap, carry, map_ofNat]

/-- A coordinate of a clause block, written out. -/
theorem cubicReduction_inl_inr (φ : Fin m → Clause n) (j : Fin m) (k : Fin 3) :
    cubicReduction φ (Sum.inl (Sum.inr j, k))
      = 12 * rename (emb (Sum.inr j)) (cubic10 k)
        + (![3, 0, 0] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k
        + (![7, 24, 8] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k
          * (remainder (φ j) j - C ((φ j 0).const * (φ j 1).const * (φ j 2).const)) := by
  have hA := block_eq φ (Sum.inr j) k
  have hB := bind₁_prodS φ j
  have hC := one_sub_rename_clausePoly (m := m) (φ j)
  have h7 : rename (Sum.inl : Var n m → Var3 n m) ((![7, 24, 8] : Fin 3 → MvPolynomial (Var n m) ℤ) k)
      = (![7, 24, 8] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k := by
    fin_cases k <;> simp [map_ofNat]
  have h7' : bind₁ (wire φ) ((![7, 24, 8] : Fin 3 → MvPolynomial (Wire n m) ℤ) k)
      = (![7, 24, 8] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k := by
    fin_cases k <;> simp [map_ofNat]
  simp only [cubicReduction, wireExt, Sum.elim_inl, reductionMap, carry, map_sub, map_mul,
    map_one, map_ofNat, h7, h7', bind₁_C_right]
  linear_combination hA
    - (![7, 24, 8] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k * hC
    + (![7, 24, 8] : Fin 3 → MvPolynomial (Var3 n m) ℤ) k * hB

theorem totalDegree_remainder (c : Clause n) (j : Fin m) :
    (remainder (m := m) c j).totalDegree ≤ 3 := by
  unfold remainder falsity sq
  exact le_trans (by td) (by norm_num)

/-- Every coordinate of the map of the reduction at degree three has degree at most three. -/
theorem totalDegree_cubicReduction (φ : Fin m → Clause n) (a : Var3 n m) :
    (cubicReduction φ a).totalDegree ≤ 3 := by
  rcases a with ⟨b | b, k⟩ | ⟨b, w⟩ | ⟨j, i⟩
  · rw [cubicReduction_inl_inl]
    have h11 := totalDegree_cubic10 k
    have h3 := Deg.vec300 (R := ℤ) (σ := Var3 n m) k
    exact le_trans (by td) (by norm_num)
  · rw [cubicReduction_inl_inr]
    have h11 := totalDegree_cubic10 k
    have h3 := Deg.vec300 (R := ℤ) (σ := Var3 n m) k
    have h7 := Deg.vec7248 (R := ℤ) (σ := Var3 n m) k
    have hr := totalDegree_remainder (m := m) (φ b) b
    exact le_trans (by td) (by norm_num)
  · exact Deg.rename _ (totalDegree_wire10 w)
  · change (wire φ (Sum.inr (j, i))).totalDegree ≤ 3
    fin_cases i <;> simp only [wire, falsity, sq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;> exact le_trans (by td) (by norm_num)

/-- **3SAT reduces to finding a zero of a map of degree three with constant Jacobian
determinant.** For every 3CNF formula `φ` with `n` variables and `m` clauses,
`cubicReduction φ` is a map of `10 n + 13 m` polynomials with integer coefficients in as many
variables, every one of degree at most three, whose Jacobian determinant is the nonzero constant
`(-3456) ^ (n + m)`, and which over every field of characteristic zero has a zero exactly when
`φ` is satisfiable. -/
theorem threeSAT_reduces_to_cubic_keller_zero (φ : Fin m → Clause n) :
    Fintype.card (Var3 n m) = 10 * n + 13 * m ∧
    (∀ a, (cubicReduction φ a).totalDegree ≤ 3) ∧
    (Matrix.of fun a b => pderiv b (cubicReduction φ a)).det = C ((-3456) ^ (n + m)) ∧
    ∀ (K : Type) [Field K] [CharZero K],
      (∃ v : Var3 n m → K, ∀ a, aeval v (cubicReduction φ a) = 0) ↔
        ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ :=
  ⟨card_var3 n m, totalDegree_cubicReduction φ, det_cubicReduction φ,
    fun _ _ _ => exists_zero_cubicReduction_iff_satisfiable φ⟩

end KellerZero
