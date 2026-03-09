import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

/--
Erdős Problem #64 (Conjectured by Erdős and Gyárfás [Er93,Er94b,Er95,Er96,Er97b,Er97c]):

Does every finite graph with minimum degree at least 3 contain a cycle of length 2^k
for some k ≥ 2?

Erdős and Gyárfás believed the answer must be negative. Liu and Montgomery [LiMo20]
proved that the answer is affirmative if the minimum degree is larger than some absolute
constant, disproving the stronger conjecture.
-/
theorem erdos_problem_64 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 3 ≤ G.minDegree) :
    ∃ k : ℕ, 2 ≤ k ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ k :=
  sorry
