import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical Finset Real

noncomputable section

/-!
# Erdős Problem #1099

Let 1 = d₁ < ⋯ < d_{τ(n)} = n be the divisors of n, and for α > 1 let
  h_α(n) = Σᵢ (d_{i+1}/dᵢ - 1)^α.

Is it true that liminf_{n→∞} h_α(n) ≪_α 1?

That is, for every α > 1, does there exist a constant C (depending on α) such
that h_α(n) ≤ C for infinitely many n?

Erdős [Er81h] remarks that n! or lcm{1,…,n} would be good candidates.
The liminf is trivially ≥ 1 (considering the term i = 1).

Proved by Vose [Vo84] who constructed a specific sequence achieving bounded
h_α(n). It remains open whether n! or lcm{1,…,n} satisfy this property.

This resembles the function G(n) = Σᵢ dᵢ/d_{i+1} considered in problem #673.

Tags: number theory, divisors
-/

/-- The sorted list of divisors of n in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- h_α(n) = Σᵢ (d_{i+1}/dᵢ - 1)^α where d₁ < ⋯ < d_{τ(n)} are the
    divisors of n in increasing order. -/
noncomputable def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

/--
Erdős Problem #1099 (Proved by Vose [Vo84]):

For every α > 1, there exists a constant C (depending on α) such that
h_α(n) ≤ C for infinitely many n, i.e., liminf_{n→∞} h_α(n) is finite.

Formally: for every α > 1, there exists C such that for every N, there
exists n ≥ N with h_α(n) ≤ C.
-/
theorem erdos_problem_1099 (α : ℝ) (hα : α > 1) :
    ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ hAlpha α n ≤ C :=
  sorry

end
