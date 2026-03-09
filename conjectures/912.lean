import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Nat Finset Filter Real

noncomputable section

/--
The p-adic valuation of n!, i.e., the exponent of prime p in the factorisation of n!.
-/
def factorialPadicVal (n p : ℕ) : ℕ :=
  (n !).factorization p

/--
The number of distinct exponents appearing in the prime factorisation of n!.
That is, h(n) = |{v_p(n!) : p prime, p ≤ n, v_p(n!) > 0}|.
-/
def h (n : ℕ) : ℕ :=
  ((n !).factorization.support.image (fun p => (n !).factorization p)).card

/--
Erdős Problem #912 [Er82c]:

If n! = ∏ pᵢ^kᵢ is the factorisation into distinct primes, let h(n) count the
number of distinct exponents kᵢ.

Prove that there exists some c > 0 such that
  h(n) ~ c · (n / log n)^(1/2)
as n → ∞.

Erdős and Selfridge proved h(n) ≍ (n / log n)^(1/2). A heuristic of Tao using
the Cramér model for the primes suggests c = √(2π) = 2.506…
-/
theorem erdos_problem_912 :
    ∃ c : ℝ, 0 < c ∧
      Asymptotics.IsLittleO atTop
        (fun n : ℕ => (h n : ℝ) - c * Real.sqrt (↑n / Real.log ↑n))
        (fun n : ℕ => c * Real.sqrt (↑n / Real.log ↑n)) :=
  sorry

end
