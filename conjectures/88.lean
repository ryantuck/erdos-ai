import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Defs

open SimpleGraph Finset Real

/-- Count edges in the induced subgraph on vertex set S:
    the number of pairs {u, v} with u, v ∈ S, u < v, and G.Adj u v. -/
def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem #88 (Proved by Kwan, Sah, Sauermann, Sawhney [KSSS22]):
For any ε > 0 there exists δ = δ(ε) > 0 such that if G is a graph on n vertices
with no independent set or clique of size ≥ ε log n then G contains an induced
subgraph with exactly m edges for all m ≤ δn².

Conjectured by Erdős and McKay.
-/
theorem erdos_problem_88 :
    ∀ ε : ℝ, ε > 0 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
          haveI := h
          G.CliqueFree ⌈ε * Real.log n⌉₊ →
          Gᶜ.CliqueFree ⌈ε * Real.log n⌉₊ →
          ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
            ∃ S : Finset (Fin n), inducedEdgeCount G S = m :=
  sorry
