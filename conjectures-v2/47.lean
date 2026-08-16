import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

/--
Erdős Problem #47 [ErGr80] [Er92c] [Er95] [Er96b] [Er97c] — PROVED (LEAN), $100 prize
(erdosproblems.com/47, accessed 2026-02-22):

"If δ > 0 and N is sufficiently large in terms of δ, and A ⊆ {1, …, N} is such that
∑_{a ∈ A} 1/a > δ log N then must there exist S ⊆ A such that ∑_{n ∈ S} 1/n = 1?"

The answer is yes: solved by Bloom [Bl21], who showed that the quantitative threshold
∑_{n ∈ A} 1/n ≫ (log log log N / log log N) · log N is sufficient (see the first
variant below). This was improved by Liu and Sawhney [LiSa24] to
∑_{n ∈ A} 1/n ≫ (log N)^{4/5 + o(1)}. Erdős speculated that perhaps even
≫ (log log N)² might be sufficient (second variant below); a construction of
Pomerance, as discussed in the appendix of [Bl21], shows that this would be best
possible.

Status and provenance:
- Page banner at capture: PROVED (LEAN), tooltip "This has been solved in the
  affirmative and the proof verified in Lean." Prize: $100.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "proved (Lean)", last update
  2025-11-28; formalized: yes (2026-07-06); prize $100; OEIS: N/A;
  tags: number theory | unit fractions.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/47.lean,
  present at HEAD dd1c2be, 2026-08-16) marks `erdos_47` as `research solved` with a
  `formal_proof using lean4 at
  https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos47.lean`
  attribute, and states `answer(True) ↔ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
  ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → δ * Real.log N < A.reciprocalSum →
  ∃ S : Finset ℕ, S ⊆ A ∧ S.reciprocalSum = 1` — the same proposition as below
  (`∀ᶠ … atTop` ⟺ `∃ N₀, ∀ N ≥ N₀`; membership in `Finset.Icc 1 N` ⟺
  `1 ≤ a ∧ a ≤ N`; `Finset.reciprocalSum` is the ℝ-valued `∑ 1/n`; the
  `S.Nonempty` conjunct here is redundant, since the empty sum is 0 ≠ 1).
- The direct assertion below is the proved affirmative direction of the page's
  yes/no question, per this corpus's convention for solved problems.

Encoding notes:
- "N sufficiently large in terms of δ" is `∃ N₀, ∀ N ≥ N₀` with δ fixed first —
  the correct dependency order.
- `A ⊆ {1, …, N}` is encoded as `∀ a ∈ A, 1 ≤ a ∧ a ≤ N`; every element of a
  witness S ⊆ A is therefore ≥ 1, so no division by zero occurs in either sum
  (and ℝ's 1/0 = 0 convention would be harmless regardless).
- `S.Nonempty` is redundant (the empty sum is 0 ≠ 1) but harmless; kept for
  readability. If 1 ∈ A then S = {1} is a legitimate trivial witness, exactly as
  in the informal problem.
- For δ > 1 the hypothesis ∑_{a ∈ A} 1/a > δ log N is unsatisfiable for large N
  (the full sum ∑_{a ≤ N} 1/a = log N + O(1)), so those δ hold vacuously — as in
  the informal statement, the content is at small δ.

References (Bl21 and LiSa24 verified against the original pipeline's fetch of
erdosproblems.com/latex/47, preserved in
claude-session-logs-formal-conjectures/c152145e-….jsonl; the Erdős-source
entries are stubs from the upstream formal-conjectures reference block —
unverified offline where noted: DEFERRED):
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980). (Stub from upstream; consistent across the corpus.)
- [Er92c] Erdős, P., _Some of my forgotten problems in number theory_.
  Hardy-Ramanujan J. (1992), 34–50. (Stub from upstream 47.lean; parts of the
  sibling corpus expand [Er92c] as _Some of my favourite problems in various
  branches of combinatorics_, Matematiche (Catania) 47 (1992) — conflicting
  expansions, unresolved offline: DEFERRED.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165–186. (Stub from upstream;
  parts of the sibling corpus expand [Er95] as Congressus Numerantium 107
  (1995) — conflicting expansions, unresolved offline: DEFERRED.)
- [Er96b] Erdős, P., _Some problems I presented or planned to present in my
  short talk_. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996),
  333–335. (Stub from upstream; consistent across the corpus.)
- [Er97c] Erdős, P., _Some of my favorite problems and results_. The
  mathematics of Paul Erdős, I (1997), 47–67. (Stub from upstream 47.lean;
  parts of the sibling corpus expand [Er97c] differently — DEFERRED.)
- [Bl21] Bloom, T. F., _On a density conjecture about unit fractions_.
  arXiv:2112.03726 (2021). (Verified via the /latex/47 fetch.)
- [LiSa24] Liu, Y. and Sawhney, M., _On further questions regarding unit
  fractions_. arXiv:2404.07113 (2024). (Verified via the /latex/47 fetch.)
- Note: upstream's reference block additionally lists [Er80] (_A survey of
  problems in combinatorial number theory_, Ann. Discrete Math. (1980),
  89–115), which does NOT appear on the 2026-02-22 page capture's citation
  line; possibly a later page edition — unverified offline: DEFERRED.

Related problems: 46, 298. Tags: number theory | unit fractions. OEIS: N/A.
Source: https://www.erdosproblems.com/47
-/
theorem erdos_problem_47 (δ : ℝ) (hδ : δ > 0) :
  ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
  ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∑ a ∈ A, (1 : ℝ) / a) > δ * Real.log N →
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 :=
sorry

/--
Bloom's quantitative theorem [Bl21], stated on the source page: the threshold
∑_{n ∈ A} 1/n ≫ (log log log N / log log N) · log N is sufficient — i.e. there
is a constant C > 0 such that for all sufficiently large N, every
A ⊆ {1, …, N} with ∑_{a ∈ A} 1/a ≥ C · (log log log N / log log N) · log N
contains a nonempty S with ∑_{n ∈ S} 1/n = 1. Since
(log log log N / log log N) → 0, this implies the δ log N statement above.

Encoding notes: the Vinogradov ≫ is rendered as `∃ C > 0` with threshold
`C * (log log log N / log log N) * log N`. For N ≤ e^e ≈ 15.2 the iterated
logarithms are ≤ 0 (Lean's `Real.log` of a nonpositive number is 0), making
the threshold nonpositive and the hypothesis trivially satisfiable — the
leading `∃ N₀` (chosen after C, with N₀ > e^e) excludes those N, so no
false-at-small-parameters hazard arises.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_47.variants.bloom_threshold :
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
  ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∑ a ∈ A, (1 : ℝ) / a) ≥
      C * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N)) * Real.log N →
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 :=
sorry

/--
Erdős's speculated strengthening, stated on the source page: "Erdős speculated
that perhaps even ≫ (log log N)² might be sufficient." I.e. there is a
constant C > 0 such that for all sufficiently large N, every A ⊆ {1, …, N}
with ∑_{a ∈ A} 1/a ≥ C · (log log N)² contains a nonempty S with
∑_{n ∈ S} 1/n = 1. This remains OPEN. A construction of Pomerance, discussed
in the appendix of [Bl21], shows that this threshold would be best possible
(the page states no precise shape for the optimality assertion, so only the
sufficiency direction is formalized).

Encoding notes: as in the Bloom variant, ≫ is `∃ C > 0`, and the leading
`∃ N₀` absorbs the small-N junk values of the iterated logarithm. The
hypothesis remains satisfiable for every C at large N (the full reciprocal sum
grows like log N ≫ (log log N)²), so the `∃ C` form is not trivially provable
by unsatisfiability.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_47.variants.loglog_squared :
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
  ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∑ a ∈ A, (1 : ℝ) / a) ≥ C * (Real.log (Real.log N)) ^ 2 →
    ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 :=
sorry
