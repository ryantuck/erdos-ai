import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Nat BigOperators Real

noncomputable section

/-- The number of distinct prime divisors of n (the arithmetic function ω(n)). -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- The sum of ω(n+i) for i in {0, 1, …, k-1}. -/
def omegaSum (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, omega (n + i)

/--
Erdős Problem #890 [ErSe67] — OPEN

If ω(n) counts the number of distinct prime factors of n, then is it true
that, for every k ≥ 1,
  liminf_{n → ∞} ∑_{0 ≤ i < k} ω(n+i) ≤ k + π(k)?

Erdős and Selfridge observe that the reverse inequality
  liminf_{n → ∞} ∑_{0 ≤ i < k} ω(n+i) ≥ k + π(k) - 1
holds for every k, by Pólya's theorem on gaps in smooth numbers.

Tags: number theory, primes
-/
theorem erdos_problem_890a :
    ∀ k : ℕ, 1 ≤ k →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        omegaSum n k ≤ k + Nat.primeCounting k :=
  sorry

/--
Erdős Problem #890, part 2 [ErSe67] — OPEN

Is it true that
  limsup_{n → ∞} (∑_{0 ≤ i < k} ω(n+i)) · (log log n / log n) = 1?

It is a classical fact that limsup_{n → ∞} ω(n) · (log log n / log n) = 1.

Tags: number theory, primes
-/
theorem erdos_problem_890b :
    ∀ k : ℕ, 1 ≤ k →
      ∀ ε : ℝ, 0 < ε →
        (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          (omegaSum n k : ℝ) * (Real.log (Real.log n) / Real.log n) < 1 + ε) ∧
        (∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
          1 - ε < (omegaSum n k : ℝ) * (Real.log (Real.log n) / Real.log n)) :=
  sorry

end
