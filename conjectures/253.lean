import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

open Filter

/--
The set of all integers representable as a sum of distinct elements from a
sequence `a : ℕ → ℕ`. That is, the set of all `∑ i in S, a i` for finite
subsets `S` of `ℕ`.
-/
def sumsetOfDistinct (a : ℕ → ℕ) : Set ℕ :=
  {n | ∃ S : Finset ℕ, n = ∑ i ∈ S, a i}

/--
Every infinite arithmetic progression contains infinitely many elements of a
given set. An infinite arithmetic progression is {b + k * d | k ∈ ℕ} for d > 0.
-/
def HitsAllArithProgressions (T : Set ℕ) : Prop :=
  ∀ b d : ℕ, d > 0 → Set.Infinite {k : ℕ | b + k * d ∈ T}

/--
Erdős Problem #253 (disproved) [Er61] [Va99,1.24]:

Let 1 ≤ a₁ < a₂ < ⋯ be an infinite sequence of integers such that
a_{i+1}/a_i → 1. If every infinite arithmetic progression contains infinitely
many integers which are the sum of distinct aᵢ, then every sufficiently large
integer is the sum of distinct aᵢ.

This was disproved by Cassels [Ca60], who constructed a sequence with
a_{i+1} - a_i < a_i^{1/2+o(1)}, every infinite arithmetic progression
containing infinitely many elements of the sequence, yet the set of integers
which are the sum of distinct elements has density 0.
-/
theorem erdos_problem_253 (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ a i)
    (hmono : StrictMono a)
    (hratio : Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1))
    (hhits : HitsAllArithProgressions (sumsetOfDistinct a)) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n ∈ sumsetOfDistinct a :=
  sorry
