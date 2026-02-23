import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical Finset Real

noncomputable section

/-!
# Erdős Problem #1100

If 1 = d₁ < ⋯ < d_{τ(n)} = n are the divisors of n, let τ⊥(n) count the
number of i for which gcd(dᵢ, dᵢ₊₁) = 1.

Part 1: Is it true that τ⊥(n)/ω(n) → ∞ for almost all n?

Part 2: Is it true that τ⊥(n) < exp((log n)^{o(1)}) for all n?
Equivalently, for every ε > 0 and sufficiently large n,
  τ⊥(n) < exp((log n)^ε).

Part 3: Let g(k) = max over squarefree n with ω(n) = k of τ⊥(n).
Determine the growth of g(k). Erdős and Simonovits proved
  (√2 + o(1))^k < g(k) < (2 - c)^k for some constant c > 0.

Tags: number theory, divisors
-/

/-- The sorted list of divisors of n in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- τ⊥(n): the number of indices i such that gcd(dᵢ, dᵢ₊₁) = 1,
    where d₁ < ⋯ < d_{τ(n)} are the divisors of n in increasing order. -/
def tauPerp (n : ℕ) : ℕ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).filter (fun p => Nat.gcd p.1 p.2 == 1)).length

/--
Erdős Problem #1100, Part 1:
For almost all n, τ⊥(n)/ω(n) → ∞. That is, for every bound M,
the natural density of {n : τ⊥(n) ≤ M · ω(n)} is zero.
-/
theorem erdos_problem_1100_part1 :
    ∀ M : ℕ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (((Finset.range N).filter (fun n =>
          tauPerp n ≤ M * n.primeFactors.card)).card : ℝ) / (N : ℝ) < ε :=
  sorry

/--
Erdős Problem #1100, Part 2:
For every ε > 0, for all sufficiently large n,
  τ⊥(n) < exp((log n)^ε).
This formalizes the conjecture that τ⊥(n) < exp((log n)^{o(1)}).
-/
theorem erdos_problem_1100_part2 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (tauPerp n : ℝ) < Real.exp ((Real.log (n : ℝ)) ^ ε) :=
  sorry

/--
Erdős Problem #1100, Part 3 (upper bound, proved by Erdős-Simonovits):
There exists c > 0 such that for all sufficiently large k, every squarefree n
with ω(n) = k satisfies τ⊥(n) < (2 - c)^k.
-/
theorem erdos_problem_1100_part3_upper :
    ∃ c : ℝ, c > 0 ∧
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∀ n : ℕ, Squarefree n → n.primeFactors.card = k →
          (tauPerp n : ℝ) < (2 - c) ^ k :=
  sorry

/--
Erdős Problem #1100, Part 3 (lower bound, proved by Erdős-Simonovits):
For every ε > 0 and sufficiently large k, there exists a squarefree n with
ω(n) = k and τ⊥(n) > (√2 - ε)^k.
-/
theorem erdos_problem_1100_part3_lower :
    ∀ ε : ℝ, ε > 0 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∃ n : ℕ, Squarefree n ∧ n.primeFactors.card = k ∧
          (tauPerp n : ℝ) > ((2 : ℝ) ^ ((1 : ℝ) / 2) - ε) ^ k :=
  sorry

end
