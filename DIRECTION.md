# A research direction: constant-Jacobian maps as an NP-hard object

26 November 2026. A proposal for the open attack on P vs NP at
[pequalnp.com](https://pequalnp.com), written for anyone who wants to pick it up. The problem
statement and the scoreboard are in [PROBLEM.md](PROBLEM.md).

**Status, 27 November 2026.** Both conditions of section 6, "when to stop", have been met.

- The certificates of the map and of the formula simulate each other: in degree for
  Nullstellensatz, polynomial calculus and sums of squares, and in circuit size for the ideal
  proof system ([COMPLEXITY.md](COMPLEXITY.md), Theorem 5). So the proof-complexity line gives
  nothing that the usual encoding of formulas does not give.
- The complex zero problem is in NP under the generalized Riemann hypothesis (COMPLEXITY.md,
  Theorem 2), and NP-hard already at degree 3 (Lean). The classification is done: NP-complete.

So the direction ends here as a road to a lower bound, and what remains of it is a classified
object and a machine-checked reduction. Two proofs of VP ≠ VNP with Lean formalisations were
announced by Anthropic and by OpenAI on 23 and 24 November 2026; we have not examined them. If
they stand, the most this chain could have delivered (section 4) is known by other means.

The text below is the note as first written, updated where a point was settled or where the
first version was wrong about what was new ([FINDINGS.md](FINDINGS.md) lists the corrections).

Every claim below carries one of five labels.

| Label | Meaning |
|---|---|
| **Lean** | Proved in [`lean/`](lean) with Lean 4 and Mathlib, from `propext`, `Classical.choice` and `Quot.sound` only |
| **Computed** | Exact or modular computer algebra, script named; not a proof |
| **Paper** | A short argument written here, not machine-checked |
| **Known** | A published theorem, cited |
| **Open** | Nobody here knows |

## 1. What changed in July 2026

A polynomial map `F : k^N → k^N` whose Jacobian determinant is a nonzero constant is called a
Keller map. The Jacobian conjecture (Keller, 1939) said that over a field of characteristic
zero every Keller map has a polynomial inverse. In that case the question "does this Keller map
have a zero?" would have had the same answer every time: yes, exactly one.

On 19 July 2026 Levent Alpöge announced an explicit Keller map in three variables that is not
injective. Lev Stambler then used it as a gadget:
[3SAT reduces to deciding whether an integer Keller map has a real zero](https://github.com/Lev-Stambler/alg-geom-TCS),
with degree 7 and `3n + 3m` variables for `n` variables and `m` clauses.

So a question that was conjectured to be trivial is NP-hard. The local condition (the
derivative is invertible everywhere, with constant determinant) leaves the global question
(is there a zero) as hard as satisfiability.

## 2. What is machine-checked here

The gadget is `F = (P, Q, R)` with `u = 1 + xy`:

    P = u^3 z + y^2 u (4 + 3xy)
    Q = y + 3x u^2 z + 3x y^2 (4 + 3xy)
    R = 2x - 3x^2 y - x^3 z

| Statement | Name in `lean/KellerZero` | Label |
|---|---|---|
| `det JF = -2`, as polynomials over any commutative ring | `det_jacobian` | Lean |
| `F` takes the value `(-1/4, 0, 0)` at three points, so the Jacobian conjecture fails in dimension three over every field of characteristic zero | `jacobian_conjecture_fails_dim_three` | Lean |
| The fibre over `(-1/4, 0, 0)` is exactly those three points | `fibre_zero` | Lean |
| No point `(t^2/12, t, 4/(3t))`, `t ≠ 0`, is a value of `F` | `omitted_curve`, `H_omitted_curve` | Lean |
| Stambler's map `K_φ`, as integer polynomials, has a zero over a field of characteristic zero exactly when `φ` is satisfiable | `exists_zero_reductionMap_iff_satisfiable` | Lean |
| One map for all formulas on a list of clauses; the formula enters only through a 0/1 target | `hitsTarget_iff_satisfiable` | Lean |
| `det JK_φ = (-3456)^(n+m)` | `Proofs.ReductionMapIsKeller` | Lean |
| All of it as one statement | `threeSAT_reduces_to_keller_zero` | Lean |

The Lean reduction theorem holds over every field of characteristic zero, the complex numbers
included, not only over the reals.

## 3. What this note adds to the paper

**3.1 The gadget misses a curve.** Stambler uses one omitted value, `Δ = (7, 24, 8)` in his
rescaled coordinates `H = 12F + (3, 0, 0)`. It lies on a curve of omitted values:

    F never takes the value (t^2/12, t, 4/(3t)),  t ≠ 0            (Lean)
    H never takes the value (t^2 + 3, 12t, 16/t), t ≠ 0            (Lean; Δ is t = 2)

Over the complex numbers nothing else is omitted, and the same holds over the real numbers
(Lean: `image_complex`, `image_real`). The reason: a target `(a, b, c)` with `c ≠ 0` is a value
exactly when the cubic `m³ - 2m² + bc·m - 2ac²` has a simple root, and the curve is where that
cubic is a perfect cube. This description was published on 20 July 2026, before this note
(Known: see the corrections in [FINDINGS.md](FINDINGS.md)); the Lean proof is what is added
here. It fits a general fact
(Paper): a Keller map over the complex numbers never omits a hypersurface `{g = 0}`, because
`g ∘ F` would be a polynomial with no zero, hence constant, and `F` would map into `{g = c}`.
So omitted sets have codimension at least two; here the set is a curve in three-space.

**3.2 One map, all formulas.** Take every possible clause `c` on `n` variables, a new
coordinate `λ_c` and a witness block `v_c`, and the map

    U_n(w, λ, v) = ( H(w_1), ..., H(w_n),  λ,  ( H(v_c) - λ_c (1 - s_c(w)) Δ )_c ).

It is again block triangular with constant Jacobian determinant (Paper), has degree 7, and does
not depend on any formula. A formula `φ` is the 0/1 target `q_φ = (0, 1_φ, 0)`, and

    φ is satisfiable   ⟺   q_φ is a value of U_n.     (Lean, as a system of equations)

So membership in the image of one explicit polynomial map whose differential is invertible
everywhere is NP-complete on 0/1 targets. Over the complex numbers the image of `U_n` is
Zariski open (Known: étale maps are open), so its complement `Ω_n` is a closed algebraic set of
codimension at least two, and the 0/1 points of `Ω_n` are exactly the unsatisfiable formulas.

**3.3 A first measurement.** For the single gadget and an omitted target `q`, the least `D`
with `1 = Σ g_i (F_i - q_i)` and `deg(g_i F_i) ≤ D` is 10, at `t = 2, 1, -3, 5/2` (Computed:
linear algebra modulo `2^61 - 1`, [`scripts/ns_degree.py`](scripts/ns_degree.py)). The system
has degree 7, so the refutation needs three more. A certificate of degree 10 that works for
every `t` at once is now explicit (Lean: `curve_certificate`).

## 4. The chain to P vs NP, and the link that is missing

A route should say how it reaches P vs NP and where it stops. This one stops early.

1. `φ` unsatisfiable ⟺ `K_φ` has no complex zero (Lean) ⟺ `1` is in the ideal of the
   coordinates of `K_φ` (Known: Nullstellensatz). An unsatisfiable formula has a certificate
   `1 = Σ g_i K_i`.
2. For the standard encoding of CNFs, a superpolynomial lower bound on the circuit size of such
   certificates, for some family of unsatisfiable formulas, implies VNP ≠ VP (Known: Grochow and
   Pitassi, the Ideal Proof System). The Keller encoding and the standard one simulate each
   other (Paper: COMPLEXITY.md, Theorem 5), so this carries over, and nothing is gained.
3. VNP ≠ VP is implied by NP ⊄ P/poly under the generalized Riemann hypothesis (Known:
   Bürgisser, 2000). It is not known to imply it.

**The missing link is step 2's hypothesis: any superpolynomial lower bound on certificate
size.** This direction brings a new object, not a new technique. By known links it reaches
VP ≠ VNP at best, the algebraic relative of P ≠ NP, not P ≠ NP itself.

What the object has that the standard encoding lacks:

- The system is square and every solution is simple (the Jacobian never vanishes). A generic
  target of the gadget has 3 preimages (Computed), so a generic target of `K_φ` has `3^(n+m)`;
  unsatisfiable targets form a thin closed set.
- NP versus coNP reads: a point outside `Ω_n` has a short proof (a preimage). Does a point
  inside the closed set `Ω_n` have one?
- Its geometry is computable at small sizes: the omitted set, certificate degrees, the number
  of preimages.

**Barriers.** A reduction relativizes and proves no lower bound. Any attempt to bound the
equations of `Ω_n` or the certificates faces the usual obstacles for algebraic circuit lower
bounds, including the algebraic natural proofs barrier (Forbes, Shpilka and Volk; Grochow,
Kumar, Saks and Saraf). Nothing here is claimed to pass them.

**Classification.** Over the complex numbers the zero problem for Keller maps is NP-hard, and
it is in NP under the generalized Riemann hypothesis (Paper: COMPLEXITY.md, Theorem 2; for
general systems the known bound is weaker, Koiran, 1996). The zeros are isolated and simple,
which is what the generic problem lacks, and that is exactly what the proof uses: a zero modulo
a prime lifts. The zeros themselves need not be small: the Keller map
`(x_1 - 2, x_2 - x_1^2, x_3 - x_2^2, ...)` has its only zero at `x_k = 2^(2^(k-1))`. Over the
reals the problem sits between NP and the existential theory of the reals, and whether it is in
NP is open.

## 5. First units

Each is one exact statement. Most were settled after the note was first written; the
statements still to prove in Lean are in [`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean).

| Kind | Statement | Status |
|---|---|---|
| prove (O1) | Over the complex numbers the gadget omits the curve and nothing else | Lean |
| prove (O2) | `det JK_φ = (-3456)^(n+m)` for the polynomial map `reductionMap φ` | Lean |
| prove (O3) | A Keller map of degree at most two is injective (Wang, 1980) | Lean |
| prove | 3SAT reduces to the zero problem for Keller maps of degree 3 | Lean: `threeSAT_reduces_to_cubic_keller_zero` |
| prove | The omitted set of the gadget over the reals | Lean: the same curve |
| prove (O4) | The Jacobian determinant of the 12-variable map of degree 3 is `-2` | Lean |
| prove (O5) | A Keller map of degree at most two is a bijection | Known; open in Lean |
| value | The least Nullstellensatz degree for the target `Δ` of the gadget (computed: 10) | an exact certificate of degree 10 is in Lean; that 9 is impossible is Computed modulo a prime |
| value | The same for `K_φ` with `φ = x ∧ ¬x` (9 variables), against the standard encoding of the same formula | at most 24 (Computed), and at least 7, the degree of the system; in general between the formula's degree (Lean) and twice it plus 18 (Paper) |
| search | A non-injective Keller map of degree 3 in fewer than 12 variables | Known: 11, published 20 July 2026; fewer is open |
| search | A non-injective Keller map of degree below 7 in three variables | open |
| search | Any non-injective Keller map in two variables (this would settle the plane Jacobian conjecture) | open |
| open | Is the zero problem for Keller maps in NP, over the complex numbers or over the reals? | complex: yes, under the generalized Riemann hypothesis (Paper); real: open |
| prove (O7) | A zero modulo a prime at which the Jacobian determinant is not zero gives a complex zero | Paper; open in Lean |
| prove (O8) | A refutation of the formula gives one of its map of at most twice the degree plus a constant | Paper; open in Lean |

## 6. When to stop

- If certificates for the Keller encoding and for the standard encoding simulate each other
  with polynomial overhead in size and degree, the proof-complexity line gives nothing the
  standard encoding does not. Stop it, and keep the formalization and the classification.
- If certificate degrees at computable sizes match the standard encoding up to a constant,
  the same.
- If the zero problem over the complex numbers is shown to be in NP, the classification is
  done: NP-complete.

Both happened on 27 November 2026; see the status at the top.

## 7. What was not checked

- The first version was written without a literature search. One was made on 27 November 2026
  (FINDINGS.md): the omitted curve (3.1) was already published; the one-map form (3.2) we did
  not find.
- That no certificate of degree 9 exists for the target `Δ` is computed modulo one prime.
- The papers of Koiran and of Kabanets and Impagliazzo were re-opened for the statements used
  in COMPLEXITY.md; the other citations are from memory.

## Sources

- L. Alpöge, announcement of an explicit three-variable counterexample to the Jacobian
  conjecture, 19 July 2026: https://x.com/__alpoge__/status/2079028340955197566
- L. Stambler, *Reducing 3SAT to Zero-Finding for Constant-Jacobian Polynomial Maps*, 2026:
  https://github.com/Lev-Stambler/alg-geom-TCS
- O.-H. Keller, *Ganze Cremona-Transformationen*, Monatsh. Math. Phys. 47 (1939).
- S. S.-S. Wang, *A Jacobian criterion for separability*, J. Algebra 65 (1980).
- H. Bass, E. Connell, D. Wright, *The Jacobian conjecture: reduction of degree and formal
  expansion of the inverse*, Bull. AMS 7 (1982).
- P. Koiran, *Hilbert's Nullstellensatz is in the polynomial hierarchy*, J. Complexity 12 (1996).
- G. Kuperberg, *Knottedness is in NP, modulo GRH*, Adv. Math. 256 (2014).
- V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*, STOC 2003.
- M. Mahajan, V. Vinay, *Determinant: combinatorics, algorithms, and complexity*, Chicago J.
  Theoret. Comput. Sci. (1997).
- E. Ben-Sasson, R. Impagliazzo, *Random CNF's are hard for the polynomial calculus*, FOCS 1999;
  M. Alekhnovich, A. Razborov, *Lower bounds for polynomial calculus: non-binomial case*, 2001.
- D. Grigoriev, *Linear lower bound on degrees of Positivstellensatz calculus proofs for the
  parity*, Theoret. Comput. Sci. 259 (2001); G. Schoenebeck, *Linear level Lasserre lower bounds
  for certain k-CSPs*, FOCS 2008.
- *A counterexample to the Jacobian conjecture*, unsigned manuscript dated 20 July 2026:
  https://www.ulam.ai/research/jacobian.pdf
- S. Gao, *Counterexamples to the Jacobian conjecture in dimensions greater than two*,
  arXiv:2608.00222; T. Shaska, *Graded Keller maps and the Jacobian Conjecture*,
  arXiv:2607.20210; M. de Bondt, *Alpöge's counterexample to the JC, economic stabilization, and
  Zhao's vanishing conjecture*, arXiv:2610.24889.
- Spacerat, *11 variable cubic jacobian conjecture counterexample*, 20 July 2026:
  https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8
- P. Bürgisser, *Cook's versus Valiant's hypothesis*, Theoret. Comput. Sci. 235 (2000).
- J. Grochow, T. Pitassi, *Circuit complexity, proof complexity, and polynomial identity
  testing: the ideal proof system*, J. ACM 65 (2018).
- M. Forbes, A. Shpilka, B. L. Volk, *Succinct hitting sets and barriers to proving lower bounds
  for algebraic circuits*, Theory Comput. 14 (2018); J. Grochow, M. Kumar, M. Saks, S. Saraf,
  *Towards an algebraic natural proofs barrier via polynomial identity testing* (2017).
