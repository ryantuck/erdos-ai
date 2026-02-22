import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1037

Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice,
and the number of distinct degrees is $> (\frac{1}{2} + \epsilon)n$. Must $G$
contain a trivial (empty or complete) subgraph of size 'much larger' than
$\log n$?

A question of Chen and Erdős [Er93, p.347]. The answer is no — Cambie, Chan,
and Hunter gave a construction of a graph on $n$ vertices with at least
$\frac{3}{4}n$ distinct degrees, every degree appears at most twice, and the
largest trivial subgraph has size $O(\log n)$.

Tags: graph theory
-/

/--
**Erdős Problem #1037** (Disproved by Cambie, Chan, Hunter) [Er93, p.347]:

The negation of the original conjecture: there exist ε > 0 and C > 0 such that
for all sufficiently large n, there exists a graph G on n vertices where every
degree occurs at most twice, the number of distinct degrees is > (1/2 + ε) · n,
and yet every clique and every independent set has size ≤ C · log n.

That is, one cannot guarantee a trivial subgraph much larger than log n.
-/
theorem erdos_problem_1037 :
    ∃ ε : ℝ, ε > 0 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ G : SimpleGraph (Fin n),
    ∃ _ : DecidableRel G.Adj,
      -- Every degree occurs at most twice
      (∀ d : ℕ, (Finset.univ.filter (fun v =>
        (Finset.univ.filter (fun w => G.Adj v w)).card = d)).card ≤ 2) ∧
      -- The number of distinct degrees is > (1/2 + ε) · n
      ((Finset.univ.image (fun v =>
        (Finset.univ.filter (fun w => G.Adj v w)).card)).card : ℝ) >
        (1 / 2 + ε) * (n : ℝ) ∧
      -- Every clique has size ≤ C · log n
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) ∧
      -- Every independent set has size ≤ C · log n
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) :=
  sorry

end
