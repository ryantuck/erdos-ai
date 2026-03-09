import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

/--
The proper divisors of n (all divisors except n itself).
-/
def Nat.properDivisors' (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).erase n

/--
A natural number n is **pseudoperfect** (or semiperfect) if n can be expressed
as the sum of some subset of its proper divisors (a distinct sum).
-/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S ∈ (Nat.properDivisors' n).powerset,
    S.sum id = n

/--
Erdős Problem #825 [BeEr74, Er74b, Er77c, Er96b]:

Is there an absolute constant C > 0 such that every integer n with
σ(n) > Cn is the distinct sum of proper divisors of n?

In other words, is there an upper bound for the abundancy index of
weird numbers? A number n with σ(n) > 2n that is not a distinct sum
of proper divisors is called weird. The conjecture asks whether
σ(n)/n is bounded for weird numbers.

This has been solved in the affirmative by Larsen.
-/
theorem erdos_problem_825 :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n > 0 →
        (((Nat.divisors n).sum id : ℕ) : ℝ) > C * (n : ℝ) →
        IsPseudoperfect n :=
  sorry
