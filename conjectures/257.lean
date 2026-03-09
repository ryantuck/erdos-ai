import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #257 [Er68d, ErGr80, Er88c]:

Let A ⊆ ℕ be an infinite set. Is ∑_{n ∈ A} 1/(2ⁿ - 1) irrational?

When A = ℕ, this equals ∑_n d(n)/2ⁿ where d(n) is the number of divisors
of n, which Erdős [Er48] proved is irrational. The case when A is the set
of primes (Problem #69) was settled by Tao and Teräväinen [TaTe25].
-/
theorem erdos_problem_257 (A : Set ℕ) (hA : A.Infinite) :
    Irrational (∑' (n : A), (1 : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)) :=
  sorry
