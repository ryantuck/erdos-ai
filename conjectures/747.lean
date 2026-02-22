import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Disjoint

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #747

How large should ℓ(n) be such that, almost surely, a random 3-uniform
hypergraph on 3n vertices with ℓ(n) edges must contain n vertex-disjoint
edges?

Asked to Erdős by Shamir in 1979 (Shamir's problem). Johansson, Kahn,
and Vu [JKV08] proved the threshold is ℓ(n) = Θ(n log n). Kahn [Ka23]
proved the sharp threshold is ~ n log n.

https://www.erdosproblems.com/747

Tags: combinatorics, hypergraphs
-/

/-- The set of all 3-element subsets of Fin N (potential hyperedges). -/
def threeEdges (N : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter (fun s => s.card = 3)

/-- The set of all 3-uniform hypergraphs on Fin N with exactly m edges. -/
def hypergraphsWithEdges (N m : ℕ) : Finset (Finset (Finset (Fin N))) :=
  (threeEdges N).powerset.filter (fun H => H.card = m)

/-- A 3-uniform hypergraph H contains a matching of size k: there exist
    k pairwise vertex-disjoint edges in H. -/
def hasMatching {N : ℕ} (H : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∃ M : Finset (Finset (Fin N)), M ⊆ H ∧ M.card = k ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- The fraction of 3-uniform hypergraphs on Fin N with m edges that
    contain a matching of size k. Returns 0 if no such hypergraphs exist. -/
noncomputable def hypergraphMatchingFraction (N m k : ℕ) : ℝ :=
  ((hypergraphsWithEdges N m).filter (fun H => hasMatching H k)).card /
  ((hypergraphsWithEdges N m).card : ℝ)

/--
Erdős Problem #747 (Shamir's problem) [Er81]:

For every ε > 0, almost surely a random 3-uniform hypergraph on 3n vertices
with at least (1 + ε) · n · log n edges contains n vertex-disjoint edges.

Formally: for every ε > 0 and δ > 0, there exists n₀ such that for all
n ≥ n₀ and all m with (1 + ε) · n · log n ≤ m ≤ C(3n, 3), the fraction
of 3-uniform hypergraphs on 3n vertices with m edges containing a perfect
matching is at least 1 − δ.

Proved by Johansson, Kahn, and Vu [JKV08]; sharp threshold by Kahn [Ka23].
-/
theorem erdos_problem_747 :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ m : ℕ, (m : ℝ) ≥ (1 + ε) * (n : ℝ) * Real.log (n : ℝ) →
        m ≤ (3 * n).choose 3 →
        hypergraphMatchingFraction (3 * n) m n ≥ 1 - δ :=
  sorry

end
