import KellerZero.Program
import KellerZero.CubicReduction

/-!
# The reduction with one checking gadget

`compactReduction φ` is a map of degree three with constant Jacobian determinant that has a
zero exactly when the 3CNF formula `φ` is satisfiable, in `10 n + ⌈m / 2⌉ + 12` variables. The
map of `CubicReduction` uses a gadget for every clause (`10 n + 13 m` variables). This one uses
`n + 1` gadgets whatever the number of clauses:

* one gadget per variable of the formula, as before;
* one variable `s` that counts the false clauses: its coordinate is `s` minus the sum over the
  clauses of the product of three falsity polynomials, a polynomial of degree three;
* a chain `r 0 = 1`, `r (i + 1) = r i * (2 i + 1 - s) * (2 i + 2 - s)`, so that the last `r` is
  `(2 L)!` when `s = 0` and `0` when `s` is one of `1, …, 2 L`;
* one gadget that checks the result: its equations are `ρ H(v) = (ρ - r L) (7, 24, 8)` with
  `ρ = (2 L)!`, solvable when `s = 0` and not when a clause is false.

The count and the chain are a computation, and a computation costs no gadget
(`KellerZero.Program`).
-/

namespace KellerZero

open MvPolynomial

variable {n m : ℕ}

/-- The computation variables: the count of false clauses, and a chain of length `L + 1`. -/
abbrev Comp (L : ℕ) := Unit ⊕ Fin (L + 1)

/-- The falsity polynomial of a literal in the wire variable that holds `x ^ 2`: `1 - h` for a
variable and `h` for a negated one. -/
noncomputable def falsH (L : ℕ) (l : Literal n) : MvPolynomial (Inner n (Comp L)) ℤ :=
  C l.const - C l.sign * X (Sum.inl (l.var, Sum.inr 3))

/-- The count variable. -/
noncomputable def countVar (L : ℕ) : MvPolynomial (Inner n (Comp L)) ℤ := X (Sum.inr (Sum.inl ()))

/-- The polynomial of each computation variable. -/
noncomputable def compactProg (φ : Fin m → Clause n) (L : ℕ) :
    Comp L → MvPolynomial (Inner n (Comp L)) ℤ
  | Sum.inl _ => ∑ j, ∏ l, falsH L (φ j l)
  | Sum.inr i => Fin.cases 1 (fun i' : Fin L =>
      X (Sum.inr (Sum.inr i'.castSucc)) * (C (2 * (i' : ℤ) + 1) - countVar L)
        * (C (2 * (i' : ℤ) + 2) - countVar L)) i

/-- A computation variable involves only variables of lower rank. -/
def compactRank (L : ℕ) : Comp L → ℕ
  | Sum.inl _ => 0
  | Sum.inr i => i + 1

/-- The result of the computation: the last variable of the chain. -/
noncomputable def compactOut (L : ℕ) : MvPolynomial (Inner n (Comp L)) ℤ :=
  X (Sum.inr (Sum.inr (Fin.last L)))

/-- The map of the reduction with one checking gadget, for a chain of length `L`. -/
noncomputable def compactMap (φ : Fin m → Clause n) (L : ℕ) :
    PVar n (Comp L) → MvPolynomial (PVar n (Comp L)) ℤ :=
  programMap (compactProg φ L) ((2 * L).factorial : ℤ) (compactOut L)

theorem card_pvar (L : ℕ) : Fintype.card (PVar n (Comp L)) = 10 * n + L + 12 := by
  simp [PVar, Inner, Comp]
  ring

/-! ## Degree and Jacobian determinant -/

theorem compactProg_zero (φ : Fin m → Clause n) (L : ℕ) :
    compactProg φ L (Sum.inr 0) = 1 := rfl

theorem compactProg_succ (φ : Fin m → Clause n) (L : ℕ) (i : Fin L) :
    compactProg φ L (Sum.inr i.succ)
      = X (Sum.inr (Sum.inr i.castSucc)) * (C (2 * (i : ℤ) + 1) - countVar L)
        * (C (2 * (i : ℤ) + 2) - countVar L) := rfl

theorem totalDegree_compactProg (φ : Fin m → Clause n) (L : ℕ) (c : Comp L) :
    (compactProg φ L c).totalDegree ≤ 3 := by
  rcases c with u | i
  · refine totalDegree_finsetSum_le fun j _ => ?_
    simp only [Fin.prod_univ_three, falsH]
    exact le_trans (by td) (by norm_num)
  · induction i using Fin.cases with
    | zero => rw [compactProg_zero]; exact Deg.one.trans (by norm_num)
    | succ i =>
      rw [compactProg_succ]
      unfold countVar
      exact le_trans (by td) (by norm_num)

theorem pderiv_compactProg (φ : Fin m → Clause n) (L : ℕ) (c d : Comp L)
    (h : compactRank L c ≤ compactRank L d) : pderiv (Sum.inr d) (compactProg φ L c) = 0 := by
  rcases c with u | i
  · simp only [compactProg, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Fin.prod_univ_three, falsH]
  · induction i using Fin.cases with
    | zero => rw [compactProg_zero]; simp
    | succ i =>
      rw [compactProg_succ]
      rcases d with u | j
      · simp [compactRank] at h
      · have hne : j ≠ i.castSucc := by
          intro hj
          simp [compactRank, hj] at h
        simp [countVar, hne, pderiv_ofNat]

/-- The Jacobian determinant of the map: a nonzero constant. -/
theorem det_compactMap (φ : Fin m → Clause n) (L : ℕ) :
    (Matrix.of fun a b => pderiv b (compactMap φ L a)).det
      = C ((-3456) ^ n * (((2 * L).factorial : ℤ) ^ 3 * (-3456))) :=
  det_programMap _ _ _ (compactRank L) (pderiv_compactProg φ L)

/-- Every coordinate has degree at most three. -/
theorem totalDegree_compactMap (φ : Fin m → Clause n) (L : ℕ) (a : PVar n (Comp L)) :
    (compactMap φ L a).totalDegree ≤ 3 :=
  totalDegree_programMap _ _ _ (totalDegree_compactProg φ L)
    ((Deg.var _).trans (by norm_num)) a

/-! ## Zeros -/

section Zeros

variable {K : Type*} [Field K]

/-- The point `(x, y, z)` of the block of variable `i`. -/
def blockPt {L : ℕ} (v : PVar n (Comp L) → K) (i : Fin n) : K × K × K :=
  (v (Sum.inl (Sum.inl (i, Sum.inl 0))), v (Sum.inl (Sum.inl (i, Sum.inl 1))),
    v (Sum.inl (Sum.inl (i, Sum.inl 2))))

/-- The value of a falsity polynomial, once the wire `h` holds the square of `x`. -/
theorem aeval_falsH {L : ℕ} (v : PVar n (Comp L) → K) (l : Literal n)
    (hh : v (Sum.inl (Sum.inl (l.var, Sum.inr 3))) = (blockPt v l.var).1 ^ 2) :
    aeval (fun a => v (Sum.inl a)) (falsH L l) = 1 - l.value (blockPt v) := by
  unfold falsH Literal.value Literal.sign Literal.const
  split_ifs <;> simp [hh]

open Classical in
/-- The count variable holds the number of false clauses. -/
theorem aeval_count [CharZero K] {L : ℕ} (φ : Fin m → Clause n) (v : PVar n (Comp L) → K)
    (hh : ∀ i, v (Sum.inl (Sum.inl (i, Sum.inr 3))) = (blockPt v i).1 ^ 2)
    (hw : ∀ i, H (blockPt v i) = (0, 0, 0)) :
    aeval (fun a => v (Sum.inl a)) (compactProg φ L (Sum.inl ()))
      = ((Finset.univ.filter fun j => ¬ ∃ k, (φ j k).Holds (decode (blockPt v))).card : K) := by
  simp only [compactProg, map_sum, map_prod]
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hprod : ∏ l, aeval (fun a => v (Sum.inl a)) (falsH L (φ j l))
      = 1 - clauseValue (φ j) (blockPt v) := by
    simp [clauseValue, aeval_falsH, hh]
  rw [hprod]
  by_cases hj : ∃ k, (φ j k).Holds (decode (blockPt v))
  · rw [clauseValue_of_holds hw (φ j) hj]
    simp [hj]
  · rw [clauseValue_of_not_holds hw (φ j) hj]
    simp [hj]

/-- The chain: `r i` is the product of `t + 1 - s` over `t < 2 i`. -/
theorem chain_eq {L : ℕ} (r : Fin (L + 1) → K) (s : K) (h0 : r 0 = 1)
    (hs : ∀ i : Fin L, r i.succ = r i.castSucc * (2 * (i : K) + 1 - s) * (2 * (i : K) + 2 - s))
    (i : Fin (L + 1)) : r i = ∏ t ∈ Finset.range (2 * (i : ℕ)), ((t : K) + 1 - s) := by
  induction i using Fin.induction with
  | zero => simp [h0]
  | succ i ih =>
    rw [hs i, ih]
    have : 2 * ((i.succ : Fin (L + 1)) : ℕ) = 2 * (i : ℕ) + 1 + 1 := by simp; ring
    rw [this, Finset.prod_range_succ, Finset.prod_range_succ]
    simp only [Fin.val_castSucc]
    push_cast
    ring

theorem prod_range_add_one (N : ℕ) :
    ∏ t ∈ Finset.range N, ((t : K) + 1) = (N.factorial : K) := by
  have h := Finset.prod_range_add_one_eq_factorial N
  exact_mod_cast congrArg (Nat.cast : ℕ → K) h

end Zeros

section Main

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- At a zero, the chain variable `r i` holds the product of `t + 1 - s` over `t < 2 i`. -/
theorem compact_chain (φ : Fin m → Clause n) (L : ℕ) (v : PVar n (Comp L) → K)
    (hc : ∀ c, v (Sum.inl (Sum.inr c)) = aeval (fun a => v (Sum.inl a)) (compactProg φ L c))
    (i : Fin (L + 1)) :
    v (Sum.inl (Sum.inr (Sum.inr i)))
      = ∏ t ∈ Finset.range (2 * (i : ℕ)), ((t : K) + 1 - v (Sum.inl (Sum.inr (Sum.inl ())))) := by
  refine chain_eq (fun i => v (Sum.inl (Sum.inr (Sum.inr i)))) _ ?_ ?_ i
  · have := hc (Sum.inr 0)
    simpa [compactProg_zero] using this
  · intro i
    have := hc (Sum.inr i.succ)
    rw [compactProg_succ] at this
    simpa [countVar] using this

/-- A zero of the map gives a satisfying assignment. -/
theorem sat_of_zero (φ : Fin m → Clause n) (L : ℕ) (hL : m ≤ 2 * L) (v : PVar n (Comp L) → K)
    (hv : ∀ a, aeval v (compactMap φ L a) = 0) : ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := (programMap_eq_zero_iff _ _ _ v).mp hv
  have hblk : ∀ i, (∀ w, aeval (fun b => v (Sum.inl (Sum.inl (i, b)))) (wire10 w) = 0) ∧
      H (blockPt v i) = (0, 0, 0) := fun i => (scaled_one_eq_zero_iff _).mp (h1 i)
  have hh : ∀ i, v (Sum.inl (Sum.inl (i, Sum.inr 3))) = (blockPt v i).1 ^ 2 :=
    fun i => wire_h_eq _ (hblk i).1
  have hw : ∀ i, H (blockPt v i) = (0, 0, 0) := fun i => (hblk i).2
  refine ⟨decode (blockPt v), ?_⟩
  by_contra hno
  obtain ⟨j0, hj0⟩ := not_forall.mp hno
  set q := (Finset.univ.filter fun j => ¬ ∃ k, (φ j k).Holds (decode (blockPt v))).card with hq
  have hq1 : 1 ≤ q :=
    Finset.card_pos.mpr ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩⟩
  have hqm : q ≤ 2 * L := by
    have : q ≤ m := (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
    omega
  have hs : v (Sum.inl (Sum.inr (Sum.inl ()))) = (q : K) := by
    rw [h2 (Sum.inl ())]
    exact aeval_count φ v hh hw
  have hout : v (Sum.inl (Sum.inr (Sum.inr (Fin.last L)))) = 0 := by
    rw [compact_chain φ L v h2, hs]
    refine Finset.prod_eq_zero (i := q - 1) (by simp; omega) ?_
    have : ((q - 1 : ℕ) : K) + 1 = q := by exact_mod_cast Nat.sub_add_cancel hq1
    rw [this, sub_self]
  have hρ : (((2 * L).factorial : ℤ) : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * L)
  have hy : ∀ k, Hc k (v (Sum.inr (Sum.inl 0))) (v (Sum.inr (Sum.inl 1))) (v (Sum.inr (Sum.inl 2)))
      = (target k : K) := by
    intro k
    have h := h3 k
    rw [aeval_scaled_inl _ _ h4 k] at h
    simp only [compactOut, aeval_X, hout, sub_zero] at h
    have h' : (((2 * L).factorial : ℤ) : K) * Hc k (v (Sum.inr (Sum.inl 0)))
        (v (Sum.inr (Sum.inl 1))) (v (Sum.inr (Sum.inl 2)))
        = (((2 * L).factorial : ℤ) : K) * (target k : K) := by rw [h]; ring
    exact mul_left_cancel₀ hρ h'
  refine H_ne_target (v (Sum.inr (Sum.inl 0)), v (Sum.inr (Sum.inl 1)), v (Sum.inr (Sum.inl 2))) ?_
  rw [← Hc_eq, hy 0, hy 1, hy 2]
  simp [target]

/-- The point with the given coordinates. -/
def pt (e : K × K × K) : Fin 3 → K := ![e.1, e.2.1, e.2.2]

/-- A satisfying assignment gives a zero of the map. -/
theorem zero_of_sat (φ : Fin m → Clause n) (L : ℕ) (σ : Fin n → Bool)
    (hσ : ∀ j, ∃ k, (φ j k).Holds σ) :
    ∃ v : PVar n (Comp L) → K, ∀ a, aeval v (compactMap φ L a) = 0 := by
  classical
  let x : Fin n × V10 → K := fun ia =>
    Sum.elim (pt (encode σ ia.1)) (lift10 (pt (encode σ ia.1))) ia.2
  let c : Comp L → K := Sum.elim (fun _ => 0) (fun i => ((2 * (i : ℕ)).factorial : K))
  let y : V10 → K := Sum.elim (pt ((0 : K), (0 : K), (-1 / 4 : K)))
    (lift10 (pt ((0 : K), (0 : K), (-1 / 4 : K))))
  let v : PVar n (Comp L) → K := Sum.elim (Sum.elim x c) y
  have hblock : ∀ i, blockPt v i = encode σ i := by
    intro i
    simp [blockPt, v, x, pt]
  have hw : ∀ i, H (blockPt v i) = (0, 0, 0) := fun i => by rw [hblock]; exact H_encode σ i
  have hh : ∀ i, v (Sum.inl (Sum.inl (i, Sum.inr 3))) = (blockPt v i).1 ^ 2 := by
    intro i
    simp [blockPt, v, x, pt, lift10]
  have hdec : decode (blockPt v) = σ := by
    have : blockPt v = encode σ := funext hblock
    rw [this, decode_encode]
  refine ⟨v, (programMap_eq_zero_iff _ _ _ v).mpr ⟨fun i a => ?_, fun cc => ?_, fun k => ?_, fun w => ?_⟩⟩
  · refine (scaled_one_eq_zero_iff _).mpr ⟨fun w => ?_, ?_⟩ a
    · exact aeval_wire10_lift (pt (encode σ i)) w
    · have := hw i
      simpa [blockPt, v, x] using this
  · rcases cc with u | i
    · have : (Finset.univ.filter fun j => ¬ ∃ k, (φ j k).Holds σ) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j _ => not_not.mpr (hσ j)
      rw [aeval_count φ v hh hw, hdec, this]
      simp [v, c]
    · induction i using Fin.cases with
      | zero => simp [compactProg_zero, v, c]
      | succ i =>
        rw [compactProg_succ]
        have hf : (2 * ((i : ℕ) + 1)).factorial
            = (2 * (i : ℕ)).factorial * (2 * (i : ℕ) + 1) * (2 * (i : ℕ) + 2) := by
          rw [show 2 * ((i : ℕ) + 1) = 2 * (i : ℕ) + 1 + 1 by ring, Nat.factorial_succ,
            Nat.factorial_succ]
          ring
        simp [countVar, v, c, hf]
  · have hwy : ∀ w, aeval (fun b => v (Sum.inr b)) (wire10 w) = 0 :=
      fun w => aeval_wire10_lift (pt ((0 : K), (0 : K), (-1 / 4 : K))) w
    rw [aeval_scaled_inl _ _ hwy k]
    have hH : Hc k ((0 : K)) 0 (-1 / 4) = 0 := by
      fin_cases k <;> simp [Hc, P, Q, R]
      norm_num
    have hout : aeval (fun a => v (Sum.inl a)) (compactOut (n := n) L)
        = (((2 * L).factorial : ℤ) : K) := by
      simp [compactOut, v, c]
    rw [hout, sub_self, mul_zero]
    simpa [v, y, pt] using Or.inr hH
  · exact aeval_wire10_lift (pt ((0 : K), (0 : K), (-1 / 4 : K))) w

end Main

/-- **3SAT reduces to the zero problem at degree three with `n + 1` gadgets.** For every 3CNF
formula `φ` with `n` variables and `m` clauses, `compactMap φ ⌈m / 2⌉` is a map of
`10 n + ⌈m / 2⌉ + 12` integer polynomials in as many variables, every one of degree at most
three, whose Jacobian determinant is a nonzero constant, and which over every field of
characteristic zero has a zero exactly when `φ` is satisfiable. -/
theorem threeSAT_reduces_with_one_checker (φ : Fin m → Clause n) :
    Fintype.card (PVar n (Comp ((m + 1) / 2))) = 10 * n + (m + 1) / 2 + 12 ∧
    (∀ a, (compactMap φ ((m + 1) / 2) a).totalDegree ≤ 3) ∧
    (Matrix.of fun a b => pderiv b (compactMap φ ((m + 1) / 2) a)).det
      = C ((-3456) ^ n * (((2 * ((m + 1) / 2)).factorial : ℤ) ^ 3 * (-3456))) ∧
    ((-3456 : ℤ) ^ n * (((2 * ((m + 1) / 2)).factorial : ℤ) ^ 3 * (-3456)) ≠ 0) ∧
    ∀ (K : Type) [Field K] [CharZero K],
      (∃ v : PVar n (Comp ((m + 1) / 2)) → K, ∀ a, aeval v (compactMap φ ((m + 1) / 2) a) = 0) ↔
        ∃ σ : Fin n → Bool, ∀ j, ∃ k, (φ j k).Holds σ := by
  refine ⟨card_pvar _, totalDegree_compactMap φ _, det_compactMap φ _, ?_, fun K _ _ => ⟨?_, ?_⟩⟩
  · have : ((2 * ((m + 1) / 2)).factorial : ℤ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    positivity
  · rintro ⟨v, hv⟩
    exact sat_of_zero φ _ (by omega) v hv
  · rintro ⟨σ, hσ⟩
    exact zero_of_sat φ _ σ hσ

end KellerZero
