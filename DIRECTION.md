# A research direction: constant-Jacobian maps as an NP-hard object

26 November 2026. A proposal for the open attack on P vs NP at
[pequalnp.com](https://pequalnp.com), written for anyone who wants to pick it up. The problem
statement and the scoreboard are in [PROBLEM.md](PROBLEM.md).

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
| `det JK_φ = (-3456)^(n+m)` | `Open.ReductionMapIsKeller` | Paper (block triangular), open in Lean |

The Lean reduction theorem holds over every field of characteristic zero, the complex numbers
included, not only over the reals.

## 3. What this note adds to the paper

**3.1 The gadget misses a curve.** Stambler uses one omitted value, `Δ = (7, 24, 8)` in his
rescaled coordinates `H = 12F + (3, 0, 0)`. It lies on a curve of omitted values:

    F never takes the value (t^2/12, t, 4/(3t)),  t ≠ 0            (Lean)
    H never takes the value (t^2 + 3, 12t, 16/t), t ≠ 0            (Lean; Δ is t = 2)

Over the complex numbers nothing else is omitted (Computed: `P = a` with `u ≠ 0` turns `Q = b`
and `R = c` into two equations in `x` and `u` whose resultant is
`a u^3 (D u^3 + (b^2 - 12a) u - 4a)` with `D = 27a^2c^2 - 18abc + 16a + b^3c - b^2`; it has no
root exactly when `b^2 = 12a` and `3bc = 4`; 29 targets off the curve and 6 on it agree, by
Gröbner bases; [`scripts/omitted_set.py`](scripts/omitted_set.py)). That is the open statement
O1. It fits a general fact (Paper): a Keller map
over the complex numbers never omits a hypersurface `{g = 0}`, because `g ∘ F` would be a
polynomial with no zero, hence constant, and `F` would map into `{g = c}`. So omitted sets have
codimension at least two; here the set is a curve in three-space.

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
has degree 7, so the refutation needs three more.

## 4. The chain to P vs NP, and the link that is missing

A route should say how it reaches P vs NP and where it stops. This one stops early.

1. `φ` unsatisfiable ⟺ `K_φ` has no complex zero (Lean) ⟺ `1` is in the ideal of the
   coordinates of `K_φ` (Known: Nullstellensatz). An unsatisfiable formula has a certificate
   `1 = Σ g_i K_i`.
2. For the standard encoding of CNFs, a superpolynomial lower bound on the circuit size of such
   certificates, for some family of unsatisfiable formulas, implies VNP ≠ VP (Known: Grochow and
   Pitassi, the Ideal Proof System). Carrying that over to the Keller encoding needs a
   simulation lemma between the two encodings (Open; expected to be routine).
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

**Classification.** Over the complex numbers the zero problem for Keller maps is a case of
Hilbert's Nullstellensatz, so it is NP-hard and in AM under the generalized Riemann hypothesis
(Known: Koiran, 1996). Over the reals it sits between NP and the existential theory of the
reals. Whether it is in NP is open in both cases. The zeros are isolated and simple, which is
what the generic problem lacks, but they need not be small: the Keller map
`(x_1 - 2, x_2 - x_1^2, x_3 - x_2^2, ...)` has its only zero at `x_k = 2^(2^(k-1))`.

## 5. First units

Each is one exact statement; the three marked O are already written in
[`lean/KellerZero/Open.lean`](lean/KellerZero/Open.lean).

| Kind | Statement |
|---|---|
| prove (O1) | Over the complex numbers the gadget omits the curve and nothing else |
| prove (O2) | `det JK_φ = (-3456)^(n+m)` for the polynomial map `reductionMap φ` |
| prove (O3) | A Keller map of degree at most two is injective (Wang, 1980): the floor of the degree track |
| value | The least Nullstellensatz degree for the target `Δ` of the gadget (computed: 10) |
| value | The same for `K_φ` with `φ = x ∧ ¬x` (9 variables), against the standard encoding of the same formula |
| search | A non-injective Keller map of degree below 7 in three variables |
| search | Any non-injective Keller map in two variables (this would settle the plane Jacobian conjecture) |
| prove | 3SAT reduces to the zero problem for Keller maps of degree 3 (expected through the reduction of Bass, Connell and Wright; degree 2 is impossible by O3) |
| prove | The omitted set of the gadget over the reals |
| open | Is the zero problem for Keller maps in NP, over the complex numbers or over the reals? |

## 6. When to stop

- If certificates for the Keller encoding and for the standard encoding simulate each other
  with polynomial overhead in size and degree, the proof-complexity line gives nothing the
  standard encoding does not. Stop it, and keep the formalization and the classification.
- If certificate degrees at computable sizes match the standard encoding up to a constant,
  the same.
- If the zero problem over the complex numbers is shown to be in NP, the classification is
  done: NP-complete.

## 7. What was not checked

- Whether the omitted curve (3.1) or the one-map form (3.2) is already in print or in the
  discussion that followed the announcement. No literature search was made.
- The certificate degree 10 is computed modulo one prime, not proved.
- Citations are from memory of the literature and were not re-opened for this note.

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
- P. Bürgisser, *Cook's versus Valiant's hypothesis*, Theoret. Comput. Sci. 235 (2000).
- J. Grochow, T. Pitassi, *Circuit complexity, proof complexity, and polynomial identity
  testing: the ideal proof system*, J. ACM 65 (2018).
- M. Forbes, A. Shpilka, B. L. Volk, *Succinct hitting sets and barriers to proving lower bounds
  for algebraic circuits*, Theory Comput. 14 (2018); J. Grochow, M. Kumar, M. Saks, S. Saraf,
  *Towards an algebraic natural proofs barrier via polynomial identity testing* (2017).
