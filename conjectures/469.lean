import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A natural number `n` is **pseudoperfect** if it can be written as a sum of
distinct proper divisors: there exists a subset S of the proper divisors of n
such that ∑_{d ∈ S} d = n.
-/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ S.sum id = n

/--
A natural number `n` is **primitive pseudoperfect** if it is pseudoperfect
but no proper divisor m | n with m < n is pseudoperfect.
These are also known as primitive pseudoperfect numbers (OEIS A006036).
-/
def IsPrimitivePseudoperfect (n : ℕ) : Prop :=
  IsPseudoperfect n ∧ ∀ m : ℕ, m ∣ n → m < n → ¬IsPseudoperfect m

/--
The sum ∑ 1/n over elements of a set A ⊆ ℕ converges, i.e., there is a
uniform upper bound on all finite partial sums.
-/
def ConvergentReciprocalSum (A : Set ℕ) : Prop :=
  ∃ M : ℝ, ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ A →
    ∑ n ∈ F, (1 : ℝ) / (n : ℝ) ≤ M

/--
Erdős Problem #469 [Er70,p.131] [BeEr74,p.620] [ErGr80,p.93]:

Let A be the set of all n such that n = d₁ + ⋯ + dₖ with dᵢ distinct proper
divisors of n, but this is not true for any m ∣ n with m < n (the primitive
pseudoperfect numbers, OEIS A006036). Does ∑_{n ∈ A} 1/n converge?
-/
theorem erdos_problem_469 :
    ConvergentReciprocalSum {n : ℕ | IsPrimitivePseudoperfect n} :=
  sorry
