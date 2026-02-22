import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #688

Define εₙ to be maximal such that there exists some choice of congruence
class aₚ for all primes n^{εₙ} < p ≤ n such that every integer in [1, n]
satisfies at least one of the congruences ≡ aₚ (mod p).

Estimate εₙ — in particular is it true that εₙ = o(1)?

Erdős could prove εₙ ≫ (log log log n) / (log log n).

See also problems #687 and #689.
-/

/-- A choice of residue classes for primes p in (n^ε, n] covers [1, n] if
    every integer m ∈ {1, ..., n} satisfies m ≡ a(p) (mod p) for some
    prime p with n^ε < p ≤ n. -/
def PrimeCoveringInRange (n : ℕ) (ε : ℝ) (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ ε < (p : ℝ) ∧ p ≤ n ∧ m % p = a p % p

/-- Erdős Problem #688 (conjecture): εₙ = o(1).
    For any fixed δ > 0, for sufficiently large n, the primes in (n^δ, n]
    cannot cover [1, n] with any choice of congruence classes. -/
theorem erdos_problem_688 :
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ¬∃ a : ℕ → ℕ, PrimeCoveringInRange n δ a :=
  sorry

/-- Known lower bound: εₙ ≫ (log log log n) / (log log n).
    For some constant C > 0, for all sufficiently large n, there exists a
    covering using primes in (n^{C · logloglog(n)/loglog(n)}, n]. -/
theorem erdos_problem_688_lower_bound :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ a : ℕ → ℕ, PrimeCoveringInRange n
        (C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ))) a :=
  sorry

end
