import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Topology

noncomputable section

/-!
# Erdős Problem #77

*Reference:* [erdosproblems.com/77](https://www.erdosproblems.com/77)
(page last edited 08 February 2026, accessed 2026-02-22; content recovered from
archived session-log captures — the live site is unreachable from the review
container).

Statement (verbatim from the site): "If $R(k)$ is the Ramsey number for $K_k$,
the minimal $n$ such that every $2$-colouring of the edges of $K_n$ contains a
monochromatic copy of $K_k$, then find the value of
$$\lim_{k\to \infty}R(k)^{1/k}.$$"

Sources: [Er61] [Er69b] [Er71, p.99] [Er81] [Er88, p.83] [Er90b, p.17]
[Er93, p.338] [Er95] [Er97c] [Er97d] [Va99, 3.50] — tags: graph theory,
ramsey theory.

Status: **OPEN**, $250 prize ("This is open, and cannot be resolved with a
finite computation."). The teorth/erdosproblems metadata mirror
(`data/problems.yaml`, commit a09c7a2, 2026-08-14) agrees: state "open", last
update 2025-08-31; prize $250; OEIS A059442; not formalized upstream (and no
`FormalConjectures/ErdosProblems/77.lean` exists at upstream HEAD dd1c2beb,
2026-08-16 — though `FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`
there defines `Combinatorics.hypergraphRamsey`, whose 2-uniform case
`hypergraphRamsey 2 k` is the same number as `diagonalRamseyNumber k` below).

Prizes (from the page remarks): the headline \$250 is for the full problem
(determining the value). Erdős offered \$100 "for just a proof of the existence
of this constant, without determining its value", and \$1000 for a proof that
the limit does not exist — "this is really a joke as [it] certainly exists" —
a prize he raised to \$10000 in [Er88].

Known bounds: Erdős proved
$$\sqrt{2}\leq \liminf_{k\to \infty}R(k)^{1/k}
  \leq \limsup_{k\to \infty}R(k)^{1/k}\leq 4.$$
The upper bound was improved to $4-\tfrac{1}{128}$ by Campos, Griffiths,
Morris, and Sahasrabudhe [CGMS23] — the first improvement below 4 — and then
to $3.7992\cdots$ by Gupta, Ndiaye, Norin, and Wei [GNNW24]. A shorter and
simpler proof of a $4-c$ bound (and a generalisation to more than two colours)
was given by Balister, Bollobás, Campos, Griffiths, Hurley, Morris,
Sahasrabudhe, and Tiba [BBCGHMST24]. In [Er93] Erdős writes "I have no idea
what the value of $\lim R(k)^{1/k}$ should be, perhaps it is $2$ but we have
no real evidence for this."

This problem is #3 in the Ramsey Theory section of the graphs problem
collection. Related OEIS sequence: A059442. See also [1029] (lower bounds for
$R(k)$; `conjectures/1029.lean` in this repo uses the identical local
definition of `diagonalRamseyNumber`) and [627] (a closely related limit).

References (provenance per entry; the pipeline's `/latex/77` fetch survives in
the session logs only as a WebFetch summary listing five references —
[BBCGHMST24] [CGMS23] [Er88] [Er93] [GNNW24]. The remaining keys are the page
header's "appears in" sources, expanded from `/latex/N` recoveries of sibling
problems where the site-global key permits, else left as honest stubs):

- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254. (Shared-key expansion from sibling `/latex`
  recoveries; DEFERRED against `/latex/77` itself.)
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof
  Techniques in Graph Theory (1969). (Corpus-consensus entry; DEFERRED.)
- [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial
  analysis_. Combinatorial Mathematics and its Applications (Proc. Conf.,
  Oxford, 1969) (1971), 97-109. (Corpus entry; the page's pointer
  [Er71, p.99] falls inside this pagination. A rival corpus reading "Topics
  in combinatorial analysis" exists for this key — DEFERRED.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to
  see solved_. Combinatorica 1 (1981), 25-42. (Shared-key expansion from the
  `/latex/1159` recovery; DEFERRED against `/latex/77` itself.)
- [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph
  theory_. Discrete Mathematics (1988), 81-92. (From the `/latex/77` WebFetch
  summary in the session logs; volume not captured. Page pointer p.83.)
- [Er90b] Erdős, P. (1990), p.17. (Key-only stub; full data DEFERRED.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae (1993), 333-350. (From the `/latex/77`
  WebFetch summary, agreeing with sibling recoveries of the same key. Page
  pointer p.338.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Shared-key
  expansion from the three agreeing `/latex/75` captures; DEFERRED against
  `/latex/77` itself.)
- [Er97c] Erdős, P., _Some of my favorite problems and results_. The
  mathematics of Paul Erdős, I (1997). (Reading confirmed by the `/latex/5`
  recovery; sibling files disagree on this key — DEFERRED.)
- [Er97d] Erdős, P., _Some recent problems and results in graph theory_.
  Discrete Math. 164 (1997), 81-85. (Shared-key expansion from the
  `/latex/19` recovery; DEFERRED against `/latex/77` itself.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §3.50. (Corpus canonical form for this key.)
- [CGMS23] Campos, M., Griffiths, S., Morris, R., and Sahasrabudhe, J., _An
  exponential improvement for diagonal Ramsey_. arXiv:2303.09521 (2023).
  (From the `/latex/77` WebFetch summary.)
- [GNNW24] Gupta, P., Ndiaye, N., Norin, S., and Wei, L., _Optimizing the CGMS
  upper bound on Ramsey numbers_. arXiv:2407.19026 (2024). (From the
  `/latex/77` WebFetch summary.)
- [BBCGHMST24] Balister, P., Bollobás, B., Campos, M., Griffiths, S.,
  Hurley, E., Morris, R., Sahasrabudhe, J., and Tiba, M., _Upper bounds for
  multicolour Ramsey numbers_. arXiv:2410.17197 (2024). (From the `/latex/77`
  WebFetch summary.)

NOTE (review pipeline): the two `variants` theorems below were added by the
Fable review from page-confirmed content, using only constructs already
present in the original file; they are NOT compile-verified. The `def` and the
main theorem are unchanged from `conjectures/77.lean`, which the original
pipeline session built successfully with `lake build`.
-/

/-- The diagonal Ramsey number R(k): the minimum N such that for every
    symmetric 2-colouring of the edges of K_N, there is a monochromatic
    clique of size k in some colour. -/
noncomputable def diagonalRamseyNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (S : Finset (Fin N)), S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b}

/--
Erdős Problem #77 [Er61]:

The limit lim_{k → ∞} R(k)^{1/k} exists, where R(k) is the diagonal
Ramsey number.

Formulated as: there exists a real number L such that R(k)^{1/k} → L
as k → ∞.

Encoding note: the problem as posed asks to *find the value* of the limit
(the \$250 question). Since the value is unknown (the problem is open) and
this pipeline has no `answer()` mechanism, the statement formalizes the
existence sub-problem — itself explicitly prized by Erdős at \$100 — in the
direction Erdős believed ("[the limit] certainly exists"). Erdős speculated
the value is "perhaps 2 but we have no real evidence for this" [Er93].
-/
theorem erdos_problem_77 :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop (nhds L) :=
  sorry

/--
Erdős Problem #77 — non-existence variant:

The limit lim_{k → ∞} R(k)^{1/k} does not exist. Erdős offered \$1000 for a
proof, remarking "this is really a joke as [it] certainly exists", and raised
the prize to \$10000 in [Er88, p.83]. This is the direct negation of
`erdos_problem_77`: exactly one of the two (open) statements is true, and
Erdős's stated belief — and the prize asymmetry — point to the existence
direction.
-/
theorem erdos_problem_77.variants.limit_does_not_exist :
    ¬ ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop (nhds L) :=
  sorry

/--
Erdős Problem #77 — known bounds (proved by Erdős; from the problem page):

√2 ≤ liminf_{k → ∞} R(k)^{1/k} ≤ limsup_{k → ∞} R(k)^{1/k} ≤ 4.

The lower bound is Erdős's 1947 probabilistic bound (R(k) > 2^{k/2} for large
k); the upper bound follows from the Erdős–Szekeres bound
R(k) ≤ C(2k-2, k-1) < 4^k.

Encoding note: stated in the ε-eventually form — for every ε > 0, eventually
in k one has 2^{1/2} − ε < R(k)^{1/k} < 4 + ε — which is equivalent to the
liminf/limsup form for real sequences. This avoids `Filter.liminf`/`limsup`
(not reachable from this file's imports, and subject to ℝ junk-value caveats
on unbounded sequences) and `Real.sqrt` (√2 is written `(2 : ℝ) ^ ((1 : ℝ)/2)`
with the real-exponent power already used in this file).
-/
theorem erdos_problem_77.variants.erdos_bounds :
    ∀ ε : ℝ, ε > 0 → ∀ᶠ (k : ℕ) in atTop,
      (2 : ℝ) ^ ((1 : ℝ) / 2) - ε <
        (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) ∧
      (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) < 4 + ε :=
  sorry

end
