import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1036

Let $G$ be a graph on $n$ vertices which does not contain a trivial (empty or
complete) graph on more than $c\log n$ vertices. Must $G$ contain at least
$2^{\Omega_c(n)}$ many induced subgraphs which are not pairwise isomorphic?

A question of Erdős and Rényi [Er93, p.346]. Proved by Shelah [Sh98].

Tags: graph theory
-/

/--
**Erdős Problem #1036** (Proved by Shelah) [Er93, p.346]:

For every c > 0, there exist δ > 0 and N₀ such that for all n ≥ N₀, if G is a
graph on n vertices with no clique and no independent set of size greater than
c · log n, then G has at least 2^{δn} pairwise non-isomorphic induced subgraphs.

Here "trivial graph" means empty (independent set) or complete (clique), and
log denotes the natural logarithm (the choice of base is absorbed by c).
-/
theorem erdos_problem_1036 :
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      -- No clique of size > c · log n
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      -- No independent set of size > c · log n
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      -- Then there exist ≥ 2^{δn} pairwise non-isomorphic induced subgraphs
      ∃ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≥ (2 : ℝ) ^ (δ * (n : ℝ)) ∧
        ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
          ¬Nonempty (G.induce (↑S : Set (Fin n)) ≃g G.induce (↑T : Set (Fin n))) :=
  sorry

end
