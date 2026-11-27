# The complexity of maps with constant Jacobian determinant

27 November 2026. A *Keller map* is a polynomial map `F` from `N`-space to itself whose Jacobian
determinant is a nonzero constant. This note asks how hard the basic questions about such maps
are, and answers most of them. It also answers a question we were asked: has someone used these
maps to prove P = NP? No. Section 1 says what exists and what such a proof would have to do.

Labels, as everywhere in this repository: **Lean** (proved in [`lean/`](lean), three standard
axioms), **Computed** (exact arithmetic, script named), **Paper** (argued here, not formalised),
**Known** (published; cited, not re-proved).

## In short

Inputs are polynomials with integer coefficients, written as lists of terms.

| Question about a map `F` | From below | From above | Where |
|---|---|---|---|
| Is the Jacobian determinant a nonzero constant? | as hard as identity testing for determinants of linear forms, already at degree 2 | coRP | §5 |
| Does `F` have a zero? Degree 2 | | always yes, exactly one | §2 |
| Does `F` have a complex zero? Degree 3 and up | NP-hard | NP, assuming the generalized Riemann hypothesis | §2, §3 |
| How many zeros? | #P-hard | | §4 |
| Does `F` have a real zero? A rational one? | NP-hard | the existential theory of the reals; decidable | §2 |
| Certificates that there is no zero: degree in Nullstellensatz, polynomial calculus, sums of squares | linear in the number of variables, for some maps | twice the formula's, plus 18 | §6 |
| Is `F` a counterexample to the Jacobian conjecture (not injective)? | | NP, assuming the same hypothesis | §7 |

So, with the hypothesis: **deciding whether a Keller map has a complex zero is NP-complete, and
it becomes so exactly at degree 3.** P = NP if and only if that problem is in P.

What is new here, as far as we could find (§9 says where we looked): the hardness at degree 3
with its Lean proof, membership in NP, the equivalence of recognition with identity testing,
the transfer of refutations, and the count. None of it is deep. None of it is a lower bound on
computation.

## 1. Has someone proved P = NP with these maps?

We searched (arXiv, GitHub, Zenodo, X, MathOverflow, Hacker News, 27 November 2026) and found no
such proof, and no such claim with a paper behind it. What there is:

- **Stambler's theorem** (22 July 2026): 3SAT reduces to "does this Keller map have a zero?".
  This is the opposite direction. It says the zero problem is *at least* as hard as 3SAT, so a
  fast algorithm for it would give P = NP. It gives no such algorithm.
- A joke that went around on 20 July ("the Jacobian conjecture implies P = NP": a false
  statement implies everything), and unrelated announcements of P = NP in the week of
  24 November with no proof posted.

What a proof of P = NP through this door would be: a polynomial-time algorithm that decides
whether a map of degree 3 with constant Jacobian determinant has a zero (§2). The natural
attempt is to follow a path. The Jacobian matrix is invertible everywhere, so a zero of
`F - (1 - s) F(x₀)` can be continued in `s` from `x₀` without ever meeting a singular point.
The attempt fails for the reason the Jacobian conjecture fails: the path can leave to infinity
in finite time. This can happen only where the straight segment from `F(x₀)` to `0` crosses the
set over which `F` is not proper. For the gadget that set is the surface where the cubic of
[FINDINGS.md](FINDINGS.md) has a double root, and two of the three preimages leave there
(Known: the manuscript of 20 July 2026 cited in FINDINGS.md). A map that is proper everywhere
is a bijection and its zero problem is trivial. The hardness lives entirely in the escape to
infinity.

In the other direction, §6 is the one place where this note proves that something is
impossible, and it is only about three weak proof systems.

## 2. Zeros: nothing at degree 2, NP-hard at degree 3

**Theorem 1 (Lean: `threeSAT_reduces_to_cubic_keller_zero`).** For every 3CNF formula `φ` with
`n` variables and `m` clauses there is a map `cubicReduction φ` of `11n + 14m` polynomials in as
many variables, with integer coefficients, such that

1. every coordinate has total degree at most 3,
2. the Jacobian determinant is the constant `(-3456)^(n+m)`,
3. over every field of characteristic zero, the map has a zero exactly when `φ` is satisfiable.

The map is computed from `φ` in linear time; its coefficients are at most 144 in absolute value
and a coordinate has at most 23 terms (Computed: `scripts/lower_degree.py formula`).

**Degree 2 (Lean: `Proofs.QuadraticKellerMapsAreInjective`; Known: Wang, 1980).** A map of
degree at most 2 with constant nonzero Jacobian determinant is injective, and in fact has a
polynomial inverse. So at degree 2 there is always exactly one zero, and 3 is the least degree
at which the question can be hard. `keller_zero_hard_exactly_from_degree_three` states the two
halves together.

Because (3) holds over every field of characteristic zero, the real, the rational and the
complex zero problems are all NP-hard at degree 3.

*How the map is built.* Stambler's map `K_φ` has degree 7: a copy of Alpöge's map for every
variable and every clause, and a product of three literal values in every clause block. A
*wire extension* (Lean: [`Wire.lean`](lean/KellerZero/Wire.lean)) adds variables `t_c` and
coordinates `s_c = t_c + (a polynomial in the old variables and earlier wires)`, and subtracts
from the old coordinates polynomials in the `s_c`. `det_wireExt` proves that this never changes
the Jacobian determinant, and `aeval_wireExt_eq_zero_iff` that it never changes the zeros. This
is the reduction of degree of Bass, Connell and Wright (1982). What has to be chosen is which
wires: eight per block, those of the eleven-variable map of degree 3 published on 20 July 2026
([gist](https://gist.github.com/Spacerat/08b4a43f6b6ca57178efabc220170ce8)), and three per
clause for the product of the literal values. `det_cubic11Map`, `totalDegree_cubic11Map` and
`cubic11Map_not_injective` check that eleven-variable map itself in Lean.

Upper bounds that are known for all systems of polynomial equations: a real zero can be decided
in the existential theory of the reals, hence in polynomial space (Known: Canny, 1988). The
rational zero problem is decidable for Keller maps, because there are finitely many complex
zeros; for general systems it is a famous open problem.

## 3. Complex zeros have short proofs

The only zero of the map `(x₁ - 2, x₂ - x₁², …, x_N - x_{N-1}²)`, which has degree 2 and
Jacobian determinant 1, is `x_k = 2^(2^(k-1))`: its last coordinate has `2^(N-1) + 1` binary
digits. So a zero cannot be the proof that a zero exists. A zero modulo a prime can.

**Theorem 2 (Paper, from Known results).** Let `F` be a map with integer coefficients whose
Jacobian determinant is a nonzero constant `c`. Then `F` has a complex zero if and only if
there are a prime `p` not dividing `c` and a point `a` with coordinates modulo `p` such that
`F(a) = 0` modulo `p`. Assuming the generalized Riemann hypothesis, `p` can be taken with a
number of digits polynomial in the size of `F`. So, under that hypothesis, "does a Keller map
have a complex zero?" is in NP, and by Theorem 1 it is NP-complete.

*Proof.* If `F(a) = 0` modulo `p` and `p` does not divide `c`, then the Jacobian matrix at `a`
is invertible modulo `p`, and Hensel's lemma lifts `a` to a zero of `F` with `p`-adic
coordinates. So the equations `F = 0` have a solution in a field of characteristic zero. If
they had no complex solution, the Nullstellensatz would give polynomials `g_i` with rational
coefficients and `Σ g_i F_i = 1`, which no solution in any field of characteristic zero
survives. This direction needs no hypothesis, and it needs nothing about `F` except that the
verifier checks `det JF(a) ≠ 0` modulo `p`, which is one determinant of numbers.

Conversely let `F` have a complex zero. Koiran (1996, Theorem 1) proved, assuming the
generalized Riemann hypothesis: for a system of `s` integer polynomial equations in `n`
unknowns, of degree at most `d` and with coefficients of at most `L` binary digits, that has a
complex solution, at least `8A(log A + 3)` primes `p ≤ x₀` have a solution of the system in the
field of `p` elements, where `A = d^(c₁n)·s·(⌈log s⌉ + L)` and `x₀` is a number with
polynomially many digits. The primes dividing `c = det JF(0)` are at most `log₂|c|`, which is
far fewer. So one of the primes counted does not divide `c`. ∎

The witness is checked by [`scripts/witness.py`](scripts/witness.py) (Computed): for the map of
a satisfiable formula, for the squaring map above with `N = 40` (the zero has 2³⁹ + 1 digits;
the witness is forty numbers modulo 5), and for the gadget over a target with one rational
and two complex preimages, where the number of witnesses modulo `p` is 3 or 1 according to
whether `-1` is a square.

**Corollary.** Assuming the generalized Riemann hypothesis, P = NP if and only if there is a
polynomial-time algorithm deciding whether a map of degree 3 with constant Jacobian determinant
has a complex zero.

For systems in general the best known bound is weaker: the class RP^NP, or Arthur–Merlin,
under the same hypothesis (Known: Koiran, 1996), and whether the problem is in NP is open. A
system without complex solutions can still have solutions modulo some primes, so there the
verifier has to count primes. For a Keller map it need not: without a complex zero there is no
zero modulo any prime that does not divide `c`. The witness has the shape of the one in
Kuperberg's proof that knottedness is in NP assuming the same hypothesis (2014): one prime and
one solution modulo it. There soundness comes from topology; here it comes from Hensel's lemma.
The argument uses only that every zero is nonsingular. So, with no promise about the input,
the question "does this square system have a complex zero at which its Jacobian determinant is
not zero?" is in NP under the hypothesis; for a Keller map it is the zero problem.

A consequence worth a line: Stambler's map for an unsatisfiable formula has no zero modulo any
prime `p ≥ 5`. In Lean this is visible for the gadget: `not_on_curve` and `zeros_of_H` in
[`Certificates.lean`](lean/KellerZero/Certificates.lean) hold over every field in which 2 and 3
are not zero.

## 4. Counting zeros

**Theorem 3 (Paper, from Lean facts; Computed on small formulas: `scripts/count_zeros.py`).**
The map of the reduction of `φ`, at degree 7 or 3, has exactly

    3^m · Σ over satisfying assignments σ of 2^(number of variables true in σ)

zeros. Give every variable `x` a twin `y` and the clauses `(x ∨ y)` and `(¬x ∨ ¬y)`: every
satisfying assignment of the new formula `φ'` makes exactly `n` variables true, so its map has
`2^n · 3^(m+2n) · #SAT(φ)` zeros. Hence counting the zeros of a map of degree 3 with constant
Jacobian determinant is #P-hard.

*Proof.* By `H_eq_zero_iff` a variable block of a zero is one of three points, with first
coordinate `0` (false) or `±1` (true), and a clause block is one of the same three points when
its clause is satisfied and does not exist otherwise. A wire extension adds no zeros and
removes none, since each wire variable is determined by the earlier ones. ∎

## 5. Recognising a Keller map is identity testing

On 21 July Stambler asked whether one can decide in polynomial time that a given system of
polynomials is a Keller map, since the determinant "may require exponentially long strings".

**Theorem 4.** (a) (Paper) The question is in coRP: compute the integer `c = det JF(0)`,
reject if `c = 0`, and accept if `det JF(r) = c` at a random point `r` with coordinates in
`{1, …, 2ND}`, where `D` is the degree. A Keller map is always accepted; any other map is
rejected with probability at least 1/2, by the Schwartz–Zippel lemma, because `det JF - c` is a
nonzero polynomial of degree at most `N(D - 1)`.

(b) (Lean: `det_jacobian_bilinearMap`, `totalDegree_bilinearMap`) For a square matrix `M(x)`
of polynomials of degree at most 1, the map `(x, y) ↦ (x, M(x)·y)` has degree at most 2 and
Jacobian determinant `det M(x)`. So deciding whether a map *of degree 2* is a Keller map
contains the problem: is the determinant of a matrix of linear forms a nonzero constant?

(c) (Paper; Computed on examples: `scripts/recognition.py`) That problem is polynomial
identity testing for algebraic branching programs. Given matrices `A₁ (1 × n₂), A₂, …,
A_L (n_L × 1)` of polynomials of degree at most 1, put them and the 1 × 1 matrix `(t)` around
a cycle of blocks in a matrix `C`. Every cycle in the graph of `C` passes through the two
blocks of size one, so two cycles are never disjoint, and expanding the determinant over cycle
covers gives `det(I - C) = 1 - t·A₁A₂⋯A_L`. This is a nonzero constant exactly when the
product is the zero polynomial.

(d) (Known) Conversely `det JF - det JF(0)` is computed by a branching program of polynomial
size (Mahajan and Vinay, 1997), so recognition reduces to identity testing for branching
programs.

So recognising Keller maps is in P exactly when identity testing for branching programs
(equivalently, for determinants of linear forms) is, already for maps of degree 2. Derandomising
that test is a central open problem, and it has consequences: an arithmetic formula is a
branching program of about the same size, so by a theorem of Kabanets and Impagliazzo (2003,
the version for formulas) a deterministic polynomial-time algorithm that recognises Keller maps
of degree 2 would show that NEXP has no arithmetic formulas of polynomial size (Known). By
Wang's theorem a map of degree 2 is a Keller map exactly when it is a polynomial automorphism,
so *recognising the polynomial automorphisms of degree 2 is the same problem*.

## 6. Refuting the map is as hard as refuting the formula

To certify that a system `a_i = 0` has no solution one can exhibit polynomials with
`Σ g_i a_i = 1`: a Nullstellensatz refutation, of degree the largest degree of a product
`g_i a_i`. Write `E(φ)` for the usual equations of a formula: `X_i² - X_i` for every variable,
and for every clause the product of `1 - X` over its positive literals and `X` over its negated
ones.

**Theorem 5.** Let `d(·)` be the least degree of a Nullstellensatz refutation.

(a) (Lean: `refutation_of_formula`) `d(E(φ)) ≤ d(K_φ)` for Stambler's map `K_φ`: a refutation
of the map gives a refutation of the formula of no larger degree.

(b) (Paper; Computed on one formula: `scripts/certificates.py`) `d(K_φ) ≤ 2·d(E(φ)) + 18`.

(c) (Paper) For the map of degree 3: `d(E(φ)) ≤ 5·d(cubicReduction φ) + 2`.

The same three inequalities hold, with the same proofs, for the degree of polynomial calculus
refutations over the rationals and of sum-of-squares refutations over the reals.

(d) (Paper) The substitutions in the proofs are given by formulas of constant size per block.
So they also turn a certificate of the ideal proof system for one system into one for the
other, with circuit size larger by a linear term: the two encodings are equivalent for that
system too.

*Proof of (a).* Substitute for every variable block the line through its two points,
`(X_i, -3X_i/2, -1/4 + 27X_i/4)`, and for every clause block the point `(0, 0, -1/4)`. The
substitution has degree 1, so it does not raise the degree of any product. It sends the three
equations of a variable block to multiples of `X_i² - X_i` (they vanish at `X_i = 0` and `1`),
and the equations of a clause block to multiples of the clause's product, because
`1 - X² = (1 - X)(1 + X)`. ∎

*Proof of (b).* Substitute `X_i = x_i²`, where `x_i` is the first variable of block `i`, in a
refutation of `E(φ)`. Two facts turn the result into a refutation of `K_φ`. First,
`x⁴ - x²` is a combination of the three equations of a variable block with products of
degree 11 (Lean: `quartic_certificate`). Second, the clause product `f_j` is a combination of
the equations of its clause block and of the blocks of its variables with products of degree
at most 24: `target_certificate` writes `1` as a combination of `H - (7, 24, 8)` of degree 10,
which gives `1 + (1 - f_j)·τ` in the ideal for a polynomial `τ` of degree 5, and
`f_j - f_j²` is a multiple of the `x⁴ - x²`. ∎

*Proof of (c).* In a refutation of the map of degree 3, substitute for every wire variable its
value as a polynomial in the old variables. The wire coordinates become zero and the other
coordinates become those of `K_φ`, of degree at most 7. The substitution has degree at most 5,
so a product of degree `d` becomes one of degree at most `5(d - 1) + 7`. Then apply (a). ∎

**Corollary (from Known lower bounds).** Random 3CNF formulas with `n` variables and a large
enough constant ratio of clauses need degree `Ω(n)`, with high probability, in polynomial
calculus (Ben-Sasson and Impagliazzo, 1999; Alekhnovich and Razborov, 2001) and in sums of
squares (Grigoriev, 2001; Schoenebeck, 2008). So there are maps of degree 3 in `N` variables with
constant Jacobian determinant and no zero such that every Nullstellensatz, polynomial calculus
or sum-of-squares certificate of this has degree `Ω(N)`. By (b) no map of the reduction is
harder to refute than its formula.

In words: for these three proof systems the Keller structure neither helps nor hurts. Whatever
is going to separate P from NP along this road has to be about stronger systems, and there the
known theorems run the other way: a lower bound for the ideal proof system would imply
VP ≠ VNP (Grochow and Pitassi, 2014), not the reverse.

Certificates of this kind for the gadget itself are short and explicit.
`curve_certificate` (Lean) is a single identity, uniform in `t`:

    x(2u - tx)·(12P - t²) + (t²x² + 2tx(u + 1) - 8u²)·(Q - t) + (t - 2y)u²·(3tR - 4) = 4t,

with `u = 1 + xy`. It shows in one line that the gadget takes no value on its omitted curve
`12P = t², Q = t, 3tR = 4`, over every field in which `2 ≠ 0`.

## 7. Is this map a counterexample to the Jacobian conjecture?

**Proposition 6 (Paper).** Let `F` have integer coefficients and Jacobian determinant a nonzero
constant `c`. If there are a prime `p` not dividing `c` and two different points `a`, `a'`
modulo `p` with `F(a) = F(a')` modulo `p`, then `F` is not injective on complex space.
Assuming the generalized Riemann hypothesis there is such a witness of polynomial size
whenever `F` is not injective. So "is this Keller map not injective?" is in NP under that
hypothesis.

*Proof.* Read `a` as a point with integer coordinates and put `y = F(a)`. Hensel's lemma lifts
`a'` to a `p`-adic point `x'` with `F(x') = y`, and `x' ≠ a` because they differ modulo `p`.
Two different points with one image exist in a field of characteristic zero, hence in the
complex numbers. Conversely, if `F` is not injective, its generic fibre has at least two
points, so there is an integer point `r` of polynomial size whose fibre has a second point;
apply Koiran's count to the system `F(x) = F(r)`, `Σ (x_i - r_i) w_i = 1`. ∎

From below we only know that the question is trivial at degree 2. Whether it is NP-hard is
open, and a construction would have to be new: every map built in this repository has a generic
fibre of `3` points for each copy of the gadget it contains, so it is never injective, whatever
the formula.

## 8. Open

1. Remove the hypothesis from Theorem 2, or show that it cannot be removed easily. The check
   of a witness needs no hypothesis; only the size of the prime does.
2. Is "not injective" NP-hard for Keller maps (§7)?
3. Is the real zero problem for Keller maps in NP? The rational one? Neither has the modular
   witness.
4. Fewer variables at degree 3 (the record is 11), and in the reduction (11 per variable, 14
   per clause).
5. A lower bound on certificates in a proof system stronger than the three of §6.

## 9. What was not checked

- The search for earlier statements of Theorems 2, 4 and 5 and Proposition 6 was by keyword on
  arXiv, GitHub, X and the web. They are short enough that some may be folklore.
- Theorem 2, Theorem 4 (a), (c), (d), Theorem 5 (b), (c) and Proposition 6 are not formalised.
- Koiran's theorem, Wang's theorem and the lower bounds for formulas are cited, not re-proved.
