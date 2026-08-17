import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Erdős Problem #88 — the Erdős–McKay conjecture

Verbatim from erdosproblems.com/88 (archived capture, accessed 2026-02-22):

"For any ε > 0 there exists δ = δ(ε) > 0 such that if G is a graph on n vertices
with no independent set or clique of size ≥ ε log n then G contains an induced
subgraph with m edges for all m ≤ δn²."

**Status: PROVED** ("This has been solved in the affirmative"), $100 prize. Status
confirmed by the teorth/erdosproblems metadata mirror (state "proved", last update
2025-08-31). Not formalized in upstream google-deepmind/formal-conjectures as of
HEAD dd1c2be.

Remarks from the problem page:

* Conjectured by Erdős and McKay, who proved it with δn² replaced by δ(log n)²
  (recorded below as `erdos_problem_88.variants.erdos_mckay_log_sq`).
* Solved by Kwan, Sah, Sauermann, and Sawhney [KSSS22].
* Erdős' original formulation also had the condition that G has ≫ n² edges, but an
  old result of Erdős and Szemerédi says that this follows from the other condition
  anyway. (Hence the extra hypothesis is intentionally omitted here: the statement
  proved is the stronger one, without it.)
* Additional thanks: Zachary Hunter and Mehtaab Sawhney.

References (keys as listed on the problem page):

[Er92b] Erdős, P. (1992). (Problem source. Full bibliographic details are not in the
recovered page or /latex/88 extraction — honest author-year stub, DEFERRED.)

[Er95] Erdős, P. (1995). (Problem source. Stub, DEFERRED, as above.)

[Er97d] Erdős, P. (1997). (Problem source. Stub, DEFERRED, as above.)

[KSSS22] Kwan, M., Sah, A., Sauermann, L., and Sawhney, M., _Anticoncentration in
Ramsey graphs and a proof of the Erdős–McKay conjecture_, arXiv:2208.02874 (2022).
(Authors, title, arXiv id and year per the archived /latex/88 extraction — the only
full citation the authoritative source provides. Reviewer knowledge, unverified
against the source: published in Forum of Mathematics, Pi 11 (2023), e21.)

Tags: graph theory, ramsey theory.

https://www.erdosproblems.com/88
-/

open SimpleGraph Finset Real

/-- Count edges in the induced subgraph on vertex set S:
    the number of pairs {u, v} with u, v ∈ S, u < v, and G.Adj u v. -/
def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem #88 [Er92b][Er95][Er97d] (Proved by Kwan, Sah, Sauermann, Sawhney [KSSS22]):
For any ε > 0 there exists δ = δ(ε) > 0 such that if G is a graph on n vertices
with no independent set or clique of size ≥ ε log n then G contains an induced
subgraph with exactly m edges for all m ≤ δn².

Conjectured by Erdős and McKay. "No clique of size ≥ ε log n" is encoded as
`G.CliqueFree ⌈ε * log n⌉₊` (clique sizes are integers, so "size ≥ x" ⟺
"size ≥ ⌈x⌉"), and "no independent set" as the same condition on the complement.
The log is natural; the universally quantified ε absorbs the base.
-/
theorem erdos_problem_88 :
    ∀ ε : ℝ, ε > 0 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
          haveI := h
          G.CliqueFree ⌈ε * log n⌉₊ →
          Gᶜ.CliqueFree ⌈ε * log n⌉₊ →
          ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
            ∃ S : Finset (Fin n), inducedEdgeCount G S = m :=
  sorry

/--
Erdős Problem #88, Erdős–McKay partial result (proved by Erdős and McKay; remark on
the problem page): the conjecture holds with the edge-count range δn² replaced by
δ(log n)².
-/
theorem erdos_problem_88.variants.erdos_mckay_log_sq :
    ∀ ε : ℝ, ε > 0 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
          haveI := h
          G.CliqueFree ⌈ε * log n⌉₊ →
          Gᶜ.CliqueFree ⌈ε * log n⌉₊ →
          ∀ m : ℕ, (m : ℝ) ≤ δ * (log n) ^ 2 →
            ∃ S : Finset (Fin n), inducedEdgeCount G S = m :=
  sorry
