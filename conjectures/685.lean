import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Nat BigOperators

noncomputable section

/-!
# Erdős Problem #685

Let ε > 0 and n be large depending on ε. Is it true that for all n^ε < k ≤ n^{1-ε},
the number of distinct prime divisors of C(n,k) is
  (1 + o(1)) · k · ∑_{k < p < n} 1/p ?
Or perhaps even when k ≥ (log n)^c?
-/

/-- The number of distinct prime divisors of n (the arithmetic function ω(n)). -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- The sum of reciprocals of primes p with k < p < n: ∑_{k < p < n} 1/p. -/
noncomputable def primeReciprocalSum (k n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter (fun p => k < p ∧ Nat.Prime p), (1 : ℝ) / p

/--
Erdős Problem #685:
For all ε ∈ (0, 1) and δ > 0, there exists N₀ such that for all n ≥ N₀ and
all k with n^ε < k ≤ n^{1 - ε}, the number of distinct prime divisors of
C(n, k) satisfies:
  |ω(C(n,k)) - k · ∑_{k < p < n} 1/p| ≤ δ · k · ∑_{k < p < n} 1/p
-/
theorem erdos_problem_685 :
    ∀ ε : ℝ, ε > 0 → ε < 1 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ k : ℕ, (n : ℝ) ^ ε < (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
    |(↑(omega (n.choose k)) : ℝ) - ↑k * primeReciprocalSum k n| ≤
      δ * ↑k * primeReciprocalSum k n :=
  sorry

end
