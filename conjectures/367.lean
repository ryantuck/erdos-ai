import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-- The 2-full part of a natural number n: the product of all prime power
    factors p^a where a ≥ 2. Equivalently, B₂(n) = n/n' where n' is the
    product of all primes dividing n exactly once. -/
def twoFullPart (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/--
Erdős Problem #367 [ErGr80,p.68]:

Let B₂(n) be the 2-full part of n (the product of prime power factors p^a
with a ≥ 2). Is it true that for every fixed k ≥ 1,

  ∏_{n ≤ m < n+k} B₂(m) ≪ n^{2+o(1)}?

Equivalently: for every k ≥ 1 and ε > 0, the product is O_{k,ε}(n^{2+ε}).

van Doorn notes that the stronger bound ≪_k n² holds trivially for k ≤ 2
but fails for all k ≥ 3 (in fact the product is ≫ n² log n infinitely often
when k = 3).
-/
theorem erdos_problem_367 :
    ∀ k : ℕ, 1 ≤ k →
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((∏ i ∈ Finset.range k, twoFullPart (n + i) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) :=
  sorry

end
