import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Filter Set

/--
A set A ⊆ ℕ is an **additive basis of order 2** if every sufficiently large
natural number can be written as a sum of two elements of A.
-/
def IsAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n

/--
Erdős Problem #326 [ErGr80]:

Let A ⊂ ℕ be an additive basis of order 2. Must there exist a subset
B = {b₁ < b₂ < ⋯} ⊆ A which is also an additive basis of order 2 such that
the limit lim_{k→∞} b_k / k² does not exist?

Here b : ℕ → ℕ is a strictly monotone enumeration of B.

Erdős originally asked whether this was true with A = B, but this was disproved
by Cassels [Ca57].
-/
theorem erdos_problem_326 (A : Set ℕ) (hA : IsAdditiveBasisOrder2 A) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ range b ⊆ A ∧
      IsAdditiveBasisOrder2 (range b) ∧
      ¬ ∃ L : ℝ, Tendsto (fun k : ℕ => (b k : ℝ) / (k : ℝ) ^ 2) atTop (nhds L) :=
  sorry
