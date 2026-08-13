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

Let f(n) be the maximum possible chromatic number of a triangle-free graph on
n vertices. Estimate f(n).

Status: OPEN (erdosproblems.com banner, with tooltip "This is open, and cannot
be resolved with a finite computation"). What remains open is the sharper
estimation of f(n); the order of magnitude is known. The best bounds available
are
  (1 - o(1))(n / log n)^{1/2} ≤ f(n) ≤ (2 + o(1))(n / log n)^{1/2}.
The upper bound is due to Davies and Illingworth [DaIl22], the lower bound
follows from a construction of Hefty, Horn, King, and Pfender [HHKP25].

One can ask a similar question for the maximum possible chromatic number of a
triangle-free graph on m edges. Let this be g(m). Davies and Illingworth
[DaIl22] prove
  g(m) ≤ (3^{5/3} + o(1)) (m / (log m)²)^{1/3},
and Kim [Ki95] gave a construction which implies g(m) ≫ (m / (log m)²)^{1/3}.
(The g(m) bounds are recorded here in prose only: formalizing them needs an
edge-count construct not otherwise present in this file.)

The function f(n) is the inverse to the function h₃(k) considered in [1013].
A generalisation of f(n) is considered in [920] (there f(n) = f_3(n), and
f_3(n) ≍ (n / log n)^{1/2} is recorded as known).

References (honest stubs — recovered from sibling files in this corpus that
carry the same keys, themselves derived from erdosproblems.com/latex pages;
journal volume numbers were not recoverable and are deliberately omitted):

[Er67c] Erdős, P., _Some remarks on chromatic graphs_. Colloquium Mathematicum
(1967), 253–256.

[DaIl22] Davies, E., Illingworth, F., _The χ-Ramsey problem for triangle-free
graphs_. SIAM J. Discrete Math. (2022), 1124–1134.

[HHKP25] Hefty, L., Horn, P., King, R. and Pfender, F., _Improving R(3,k) in
just two bites_. arXiv:2510.19718 (2025).

[Ki95] Kim, J. H., _The Ramsey number R(3,t) has order of magnitude t²/log t_.
Random Structures and Algorithms (1995), 173–207.

https://www.erdosproblems.com/1104
Page last edited 21 January 2026; accessed 2026-03-09.
Tags: graph theory, chromatic number
-/

/-- `erdos1104_f n`: the maximum chromatic number of a triangle-free graph on n
    vertices. Defined as the supremum over all triangle-free simple graphs on
    `Fin n` of their chromatic number.

    The supremum is a genuine maximum: the defining set is nonempty (the empty
    graph `⊥` is triangle-free, contributing 0 for n = 0 and 1 for n ≥ 1) and
    bounded above by n (every graph on `Fin n` is n-colorable), so `Nat.sSup`
    never takes its unbounded junk value. -/
noncomputable def erdos1104_f (n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 3 ∧ G.chromaticNumber = (c : ℕ∞)}

/--
Erdős Problem #1104 [Er67c]:

There exist constants c₁, c₂ > 0 such that for all sufficiently large n,
  c₁ · (n / log n)^{1/2} ≤ f(n) ≤ c₂ · (n / log n)^{1/2}.

This is the known Θ-form of the answer to "Estimate f(n)": the upper bound is
due to Davies and Illingworth [DaIl22], the lower bound to Hefty, Horn, King,
and Pfender [HHKP25]. The sharper estimation (the page's bounds have constants
1 - o(1) and 2 + o(1); see the variants below) remains open.

(Any proof must take N₀ ≥ 2: for n ∈ {0, 1}, log n = 0 and the right-hand
side collapses to 0 under Lean's division-by-zero convention, so the upper
bound would fail at n = 1. The existential N₀ makes this harmless.)
-/
theorem erdos_problem_1104 :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c₁ * ((n : ℝ) / log (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (erdos1104_f n : ℝ) ∧
      (erdos1104_f n : ℝ)
        ≤ c₂ * ((n : ℝ) / log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Lower bound with the sharp constant (Hefty–Horn–King–Pfender [HHKP25]):
  f(n) ≥ (1 - o(1)) · (n / log n)^{1/2},
i.e. for every ε > 0 and all sufficiently large n,
  (1 - ε) · (n / log n)^{1/2} ≤ f(n).
SOLVED (this bound is a theorem; page-confirmed).
-/
theorem erdos_problem_1104.variants.lower_hhkp :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) / log (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (erdos1104_f n : ℝ) :=
  sorry

/--
Upper bound with the sharp constant (Davies–Illingworth [DaIl22]):
  f(n) ≤ (2 + o(1)) · (n / log n)^{1/2},
i.e. for every ε > 0 and all sufficiently large n,
  f(n) ≤ (2 + ε) · (n / log n)^{1/2}.
SOLVED (this bound is a theorem; page-confirmed).
-/
theorem erdos_problem_1104.variants.upper_davies_illingworth :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos1104_f n : ℝ)
        ≤ (2 + ε) * ((n : ℝ) / log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

end
