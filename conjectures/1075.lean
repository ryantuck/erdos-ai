import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1075

Let r ≥ 3. There exists c_r > r^{-r} such that, for any ε > 0, if n is
sufficiently large, the following holds.

Any r-uniform hypergraph on n vertices with at least (1+ε)(n/r)^r many edges
contains a subgraph on m vertices with at least c_r · m^r edges, where
m = m(n) → ∞ as n → ∞.
-/

/-- An r-uniform hypergraph on n vertices. -/
structure UniformHypergraph (n r : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- The subhypergraph of H induced by a vertex set S: all edges entirely within S. -/
def UniformHypergraph.inducedSubgraph {n r : ℕ}
    (H : UniformHypergraph n r) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.edges.filter (fun e => e ⊆ S)

/--
Erdős Problem #1075:

For every r ≥ 3, there exists c_r > r^{-r} such that for any ε > 0,
for any target size M, for all sufficiently large n, any r-uniform hypergraph
on n vertices with at least (1+ε)(n/r)^r edges contains a vertex subset S
with |S| ≥ M and at least c_r · |S|^r edges within S.

The condition "m → ∞ as n → ∞" is captured by the universal quantifier over M:
for every M, eventually (for large n) we can find a subgraph on ≥ M vertices.
-/
theorem erdos_problem_1075 (r : ℕ) (hr : r ≥ 3) :
    ∃ c_r : ℝ, c_r > 1 / (r : ℝ) ^ r ∧
    ∀ ε : ℝ, ε > 0 →
    ∀ M : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : UniformHypergraph n r,
    (H.edges.card : ℝ) ≥ (1 + ε) * ((n : ℝ) / r) ^ r →
    ∃ S : Finset (Fin n),
      S.card ≥ M ∧
      ((H.inducedSubgraph S).card : ℝ) ≥ c_r * (S.card : ℝ) ^ r :=
  sorry

end
