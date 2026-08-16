import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #22 (Bollobás–Erdős Ramsey–Turán Conjecture)

Let ε > 0 and n be sufficiently large depending on ε. Is there a graph on n
vertices with ≥ n²/8 many edges which contains no K₄ such that the largest
independent set has size at most εn?

Equivalently: rt(n; 4, εn) ≥ n²/8 for sufficiently large n, where rt(n; k, ℓ)
is the Ramsey–Turán number.

**Status: PROVED** ("This has been solved in the affirmative." —
erdosproblems.com/22, accessed 2026-02-24; the teorth/erdosproblems metadata
mirror agrees: state "proved", last update 2025-08-31).

Conjectured by Bollobás and Erdős [BoEr76], who proved the existence of such
a graph with (1/8 + o(1))n² many edges. Proved by Fox, Loh, and Zhao [FLZ15],
who showed that for every n ≥ 1 there exists a K₄-free graph on n vertices
with ≥ n²/8 edges and independence number ≪ (log log n)^{3/2} / (log n)^{1/2} · n.

Together with Szemerédi's matching upper bound rt(n; 4, εn) ≤ (1/8 + o(1))n²
[Sz72], this determines the Ramsey–Turán density of K₄ to be 1/8. (The
Szemerédi complement is recorded here from the upstream formal-conjectures
file for this problem, not from the erdosproblems.com page, and is therefore
documented but not formalized as a variant below.)

## References

- [BoEr76] Bollobás, B. and Erdős, P., *On a Ramsey-Turán type problem*.
  J. Combin. Theory Ser. B 21 (1976), 166–168.
- [Er90] Erdős, P., *Some of my favourite unsolved problems*. A tribute to
  Paul Erdős (1990), 467–478.
- [FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., *The critical window for the
  classical Ramsey-Turán problem*. Combinatorica 35 (2015), 435–476.
- [Sz72] Szemerédi, E., *On graphs containing no complete subgraph with 4
  vertices* (Hungarian). Mat. Lapok 23 (1972), 113–116.

Provenance of bibliographic data: the erdosproblems.com/22 page capture in
the session logs lists the citation keys [BoEr76] and [Er90] as problem
sources and cites [FLZ15] in the remarks, but carries no journal data (the
site loads references via separate `/bibs/` requests, not captured). The
full entries above are taken from the upstream
google-deepmind/formal-conjectures file `FormalConjectures/ErdosProblems/22.lean`
(HEAD of 2026-08-16) and, for [Er90], corroborated by multiple sibling files
of that corpus; none of it is verified against `erdosproblems.com/latex/22`.

See also Erdős Problem #615 (page-confirmed cross-reference), a closely
related Ramsey–Turán problem; `conjectures/615.lean` in this repository
defines the Ramsey–Turán number rt(n; k, ℓ) explicitly.

Additional thanks (per the page): Mehtaab Sawhney.
Related OEIS sequences: "Possible" (none listed on the page).

Tags: graph theory
https://www.erdosproblems.com/22
-/

/--
**Erdős Problem #22** (Bollobás–Erdős Conjecture on Ramsey–Turán numbers,
proved by Fox, Loh, and Zhao [FLZ15]):

For every ε > 0, for all sufficiently large n, there exists a graph G on n
vertices such that:
- G has at least n²/8 edges,
- G contains no K₄ (no clique of size 4),
- every independent set in G has size at most ε·n.

The source poses this as a yes/no question ("Is there a graph…?"); it was
answered affirmatively by [FLZ15], so per this pipeline's convention the
true (affirmative) direction is asserted directly.
-/
theorem erdos_problem_22 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          (n : ℝ) ^ 2 / 8 ≤ (G.edgeSet.ncard : ℝ) ∧
          G.CliqueFree 4 ∧
          (∀ s : Finset (Fin n), G.IsIndepSet ↑s → (s.card : ℝ) ≤ ε * (n : ℝ)) :=
  sorry

/--
**Variant (Bollobás–Erdős construction [BoEr76], page-confirmed):** the
original evidence for the conjecture. For every ε > 0 and δ > 0, for all
sufficiently large n there is a K₄-free graph on n vertices whose independent
sets all have size at most ε·n and which has at least (1/8 − δ)n² edges —
i.e. such graphs exist with (1/8 + o(1))n² many edges, δ capturing the o(1)
loss against the sharp n²/8 of the main statement.
-/
theorem erdos_problem_22.variants.bollobas_erdos_lower :
    ∀ ε : ℝ, ε > 0 → ∀ δ : ℝ, δ > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          (1 / 8 - δ) * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) ∧
          G.CliqueFree 4 ∧
          (∀ s : Finset (Fin n), G.IsIndepSet ↑s → (s.card : ℝ) ≤ ε * (n : ℝ)) :=
  sorry

/--
**Variant (quantitative Fox–Loh–Zhao bound [FLZ15], page-confirmed):** there
is a constant C > 0 such that for all sufficiently large n there exists a
K₄-free graph on n vertices with at least n²/8 edges whose independent sets
all have size at most C · (log log n)^{3/2} / (log n)^{1/2} · n — much
stronger than the ε·n of the main statement.

Note on the quantifier: the page states this "for every n ≥ 1" with an
implicit ≪-constant. The literal all-n-≥-1 rendering is false under Lean's
real-arithmetic conventions at small n (at n = 1, `Real.log 1 = 0` makes the
bound 0 while a single vertex is an independent set of size 1; at n = 2,
`Real.log (Real.log 2)` is negative and `rpow` on a negative base is a junk
value), so the standard eventual form is used, matching the upstream
formal-conjectures rendering (`∀ᶠ n in atTop`).
-/
theorem erdos_problem_22.variants.fox_loh_zhao :
    ∃ C : ℝ, C > 0 ∧
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          (n : ℝ) ^ 2 / 8 ≤ (G.edgeSet.ncard : ℝ) ∧
          G.CliqueFree 4 ∧
          (∀ s : Finset (Fin n), G.IsIndepSet ↑s →
            (s.card : ℝ) ≤
              C * (Real.log (Real.log n)) ^ (3 / 2 : ℝ)
                / (Real.log n) ^ (1 / 2 : ℝ) * (n : ℝ)) :=
  sorry
