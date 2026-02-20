import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.GCDMonoid.BigOperators

open scoped BigOperators

/--
For d ≥ 1 and k ≥ 0, P(d, k) is the set of non-negative integers expressible
as a sum of distinct powers d^i with i ≥ k.
-/
def P (d k : ℕ) : Set ℕ :=
  { n : ℕ | ∃ S : Finset ℕ, (∀ i ∈ S, k ≤ i) ∧ n = ∑ i ∈ S, d ^ i }

/--
n is (bases, k)-representable if n = ∑_{d ∈ bases} a_d where each a_d ∈ P(d, k).
Since 0 ∈ P(d, k) for all d, k (the empty sum), setting a_d = 0 corresponds to
the c_d = 0 case in the sum ∑_i c_i a_i with c_i ∈ {0, 1} and a_i ∈ P(d_i, k).
-/
def isRepresentable (bases : Finset ℕ) (k : ℕ) (n : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ d ∈ bases, f d ∈ P d k) ∧ n = ∑ d ∈ bases, f d

/--
Erdős Problem #124, Question 1 (RESOLVED — proved positively by Aristotle/Alexeev):

For any integers 3 ≤ d_1 < d_2 < ⋯ < d_r satisfying ∑ 1/(d_i - 1) ≥ 1,
all sufficiently large integers can be written as ∑_i c_i a_i where c_i ∈ {0,1}
and a_i ∈ P(d_i, 0).

Here bases is the set {d_1, ..., d_r}; elements of a Finset are automatically
distinct, capturing the d_1 < ⋯ < d_r condition up to ordering.
-/
theorem erdos_problem_124_part1 :
    ∀ bases : Finset ℕ,
      (∀ d ∈ bases, 3 ≤ d) →
      (1 : ℝ) ≤ ∑ d ∈ bases, (1 : ℝ) / ((d : ℝ) - 1) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → isRepresentable bases 0 n :=
  sorry

/--
Erdős Problem #124, Question 2 — Conjecture of Burr, Erdős, Graham, and Li [BEGL96]:

For any integers 3 ≤ d_1 < d_2 < ⋯ < d_r with ∑ 1/(d_i - 1) ≥ 1 and
gcd(d_1, ..., d_r) = 1, and for any k ≥ 1, all sufficiently large integers can
be written as ∑_i c_i a_i where c_i ∈ {0,1} and a_i ∈ P(d_i, k).

Proved for {3, 4, 7} by Burr-Erdős-Graham-Li. Still open in general.
-/
theorem erdos_problem_124_part2 :
    ∀ bases : Finset ℕ,
      (∀ d ∈ bases, 3 ≤ d) →
      (1 : ℝ) ≤ ∑ d ∈ bases, (1 : ℝ) / ((d : ℝ) - 1) →
      bases.gcd id = 1 →
      ∀ k : ℕ, 1 ≤ k →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → isRepresentable bases k n :=
  sorry
