import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

/--
A set A ⊆ ℕ has natural density zero: for every ε > 0, for all sufficiently large n,
|A ∩ {0, ..., n}| ≤ ε · n.
-/
def HasDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Set.ncard (A ∩ Set.Iic n) : ℝ) ≤ ε * (n : ℝ)

/--
Erdős Problem #72 (Proved):
Is there a set A ⊂ ℕ of density 0 and a constant c > 0 such that every graph on
sufficiently many vertices with average degree ≥ c contains a cycle whose length is in A?

Solved affirmatively by Verstraëte [Ve05] (non-constructive proof).
Liu and Montgomery [LiMo20] proved this holds even when A is the set of powers of 2.
-/
theorem erdos_problem_72 :
    ∃ (A : Set ℕ), HasDensityZero A ∧
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), k ∈ A ∧ ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k :=
  sorry
