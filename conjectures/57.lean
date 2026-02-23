import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open SimpleGraph Finset

/--
Erdős Problem #57 (Conjectured by Erdős-Hajnal [ErHa66], proved by Liu-Montgomery [LiMo20]):
If G is a graph with infinite chromatic number and a₁ < a₂ < ⋯ are the lengths of the odd
cycles of G, then ∑ 1/aᵢ = ∞.

We formalize "∑ 1/aᵢ = ∞" as: for any real bound B, there exists a finite set T of odd
natural numbers, each of which is the length of some cycle in G, whose reciprocals sum to
at least B.
-/
theorem erdos_problem_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ (B : ℝ), ∃ (T : Finset ℕ),
      (∀ n ∈ T, Odd n ∧ ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n) ∧
      B ≤ ∑ n ∈ T, (1 / (n : ℝ)) :=
  sorry
