import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Nat

noncomputable section

/-!
# Erdős Problem #824

Let h(x) count the number of integers 1 ≤ a < b < x such that (a,b) = 1 and
σ(a) = σ(b), where σ is the sum of divisors function.

Is it true that h(x) > x^{2-o(1)}?

Erdős [Er74b] proved that limsup h(x)/x = ∞, and claimed a similar proof for
this problem. A complete proof that h(x)/x → ∞ was provided by Pollack and
Pomerance [PoPo16].
-/

/-- The sum of divisors function σ(n) = Σ_{d | n} d. -/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- h(x) counts the number of pairs of coprime integers 1 ≤ a < b < x
    with equal sum-of-divisors values. -/
def erdos824_h (x : ℕ) : ℕ :=
  ((Finset.range x ×ˢ Finset.range x).filter
    (fun p => 0 < p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      sumDivisors p.1 = sumDivisors p.2)).card

/--
Erdős Problem #824 [Er59c, Er74b]:

Is it true that h(x) > x^{2-o(1)}? Equivalently, for every ε > 0,
for all sufficiently large x, h(x) > x^{2-ε}.
-/
theorem erdos_problem_824 :
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (erdos824_h x : ℝ) > (x : ℝ) ^ ((2 : ℝ) - ε) :=
  sorry

end
