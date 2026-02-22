import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #690

Let $d_k(p)$ be the density of those integers whose $k$-th smallest prime factor
is $p$ (i.e. if $p_1 < p_2 < \cdots$ are the primes dividing $n$ then $p_k = p$).

For fixed $k ≥ 1$, is $d_k(p)$ unimodal in $p$? That is, does it first increase
in $p$ until its maximum then decrease?

Erdős believed this is not always the case, but could not disprove it.
Cambie showed that $d_k(p)$ is unimodal for $1 ≤ k ≤ 3$ and is not unimodal
for $4 ≤ k ≤ 20$.

Reference: [Er79e]
https://www.erdosproblems.com/690
-/

/-- The sorted list of distinct prime factors of n in increasing order. -/
noncomputable def sortedPrimeFactors (n : ℕ) : List ℕ :=
  (Nat.primeFactors n).sort (· ≤ ·)

/-- The k-th smallest prime factor of n (1-indexed).
    Returns 0 if n has fewer than k distinct prime factors. -/
noncomputable def kthSmallestPrimeFactor (n : ℕ) (k : ℕ) : ℕ :=
  (sortedPrimeFactors n).getD (k - 1) 0

/-- Count of positive integers in {1, ..., N} whose k-th smallest prime
    factor is p. -/
noncomputable def countKthPrimeFactor (k p N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => kthSmallestPrimeFactor (n + 1) k = p)).card

/-- A function on primes is unimodal if there exists a prime m such that
    f is non-decreasing on primes ≤ m and non-increasing on primes ≥ m. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, Nat.Prime m ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → q ≤ m → f p ≤ f q) ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → m ≤ p → p ≤ q → f q ≤ f p)

/--
Erdős Problem #690:

For each fixed k ≥ 1, the density d_k(p) of positive integers whose k-th
smallest prime factor is p is unimodal in p.

This is stated as the positive answer to Erdős's question. Erdős believed the
answer is negative. Cambie confirmed d_k(p) is unimodal for 1 ≤ k ≤ 3 but
not for 4 ≤ k ≤ 20.
-/
theorem erdos_problem_690 :
    ∀ k : ℕ, k ≥ 1 →
    ∃ d_k : ℕ → ℝ,
      (∀ p : ℕ, Nat.Prime p →
        Filter.Tendsto (fun N : ℕ =>
          (countKthPrimeFactor k p (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
          atTop (nhds (d_k p))) ∧
      IsUnimodalOnPrimes d_k :=
  sorry

end
