-- [AI-Generated]: Erdős Problem 1104 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #1104

*Source:* [erdosproblems.com/1104](https://www.erdosproblems.com/1104) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
21 January 2026, captured 2026-03-09). [Er67c]

Let f(n) be the maximum possible chromatic number of a triangle-free graph on
n vertices. Estimate f(n).

The best bounds available are
  (1 - o(1))(n / log n)^{1/2} ≤ f(n) ≤ (2 + o(1))(n / log n)^{1/2}.
The upper bound is due to Davies and Illingworth [DaIl22], the lower bound
follows from a construction of Hefty, Horn, King, and Pfender [HHKP25].

## What is open

The order of magnitude f(n) ≍ (n / log n)^{1/2} is **known**: it follows from the two
bounds above. It is stated below as `erdos_problem_1104`, which is a solved statement and
not the open problem. The open part of "Estimate f(n)" is the asymptotic constant, which
the best bounds place between 1 and 2. The page states no conjecture about that constant,
so no open formal statement is given here. (The upstream formal-conjectures file likewise
formalizes only the solved bounds and leaves the main statement as a TODO.)

Further remarks on the source page:
* The analogous question for the maximum chromatic number g(m) of a triangle-free graph
  with m edges: Davies and Illingworth [DaIl22] prove
  g(m) ≤ (3^{5/3} + o(1)) (m / (log m)²)^{1/3}, and Kim [Ki95] gave a construction which
  implies g(m) ≫ (m / (log m)²)^{1/3}. (Not formalized: it needs an edge-count constraint,
  which is not among this file's constructs.)
* The function f(n) is the inverse to the function h₃(k) considered in [1013].
* A generalisation of f(n) is considered in [920].

Tags: graph theory, chromatic number. OEIS: "possible" (A292528 in the
teorth/erdosproblems mirror). The page records an upstream formalised statement.

## References

* [Er67c] Erdős, P., _Some remarks on chromatic graphs_. Colloquium Mathematicum (1967),
  253–256.
* [DaIl22] Davies, Ewan and Illingworth, Freddie, _The χ-Ramsey problem for
  triangle-free graphs_. SIAM J. Discrete Math. (2022), 1124–1134.
* [HHKP25] Hefty, Z., Horn, P., King, D., and Pfender, F., _Improving R(3,k) in just two
  bites_. arXiv:2510.19718 (2025).
* [Ki95] Kim, J. H., _The Ramsey number R(3,t) has order of magnitude t²/log t_. Random
  Structures and Algorithms (1995), 173–207.

(Provenance: the original pipeline's fetches of `erdosproblems.com/latex/627` for [Er67c],
`/latex/1011` for [DaIl22] and [HHKP25], and `/latex/610` and `/latex/165` for [Ki95]. Each
cites the same key. Volume numbers are not in those extractions. The gloss "Hefty, L.,
Horn, P., King, R. and Pfender, F." found in archived styled files has the wrong
initials.)
-/

/-- `erdos1104_f n`: the maximum chromatic number of a triangle-free graph on n
    vertices. Defined as the supremum over all triangle-free simple graphs on
    `Fin n` of their chromatic number. The set is nonempty (it contains the chromatic
    number of the empty graph) and bounded by `n`, so the `sSup` is a genuine maximum.
    For example, `erdos1104_f n` for `n = 0, …, 7` is `0, 1, 2, 2, 2, 3, 3, 3`, the jump
    at 5 coming from the 5-cycle. -/
noncomputable def erdos1104_f (n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 3 ∧ G.chromaticNumber = (c : ℕ∞)}

/--
Erdős Problem #1104 [Er67c] — order of magnitude (SOLVED; not the open part):

There exist constants c₁, c₂ > 0 such that for all sufficiently large n,
  c₁ · (n / log n)^{1/2} ≤ f(n) ≤ c₂ · (n / log n)^{1/2}.

This is a known consequence of the bounds of [HHKP25] and [DaIl22]
(`erdos_problem_1104.variants.lower` and `.upper`). Earlier results already gave the
order of magnitude, e.g. [Ki95] for the lower bound. What remains open is the asymptotic
constant; see the module docstring.
-/
theorem erdos_problem_1104 :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c₁ * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (erdos1104_f n : ℝ) ∧
      (erdos1104_f n : ℝ)
        ≤ c₂ * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Lower bound [HHKP25] (SOLVED): f(n) ≥ (1 - o(1)) (n / log n)^{1/2}, i.e. for every
ε > 0, f(n) ≥ (1 - ε) (n / log n)^{1/2} for all sufficiently large n.
-/
theorem erdos_problem_1104.variants.lower :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (erdos1104_f n : ℝ) :=
  sorry

/--
Upper bound [DaIl22] (SOLVED): f(n) ≤ (2 + o(1)) (n / log n)^{1/2}, i.e. for every
ε > 0, f(n) ≤ (2 + ε) (n / log n)^{1/2} for all sufficiently large n.
-/
theorem erdos_problem_1104.variants.upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos1104_f n : ℝ)
        ≤ (2 + ε) * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

end
