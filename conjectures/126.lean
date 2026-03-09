import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

noncomputable section

/--
The number of distinct prime factors of the product ∏_{(a,b) ∈ A.offDiag} (a + b).
-/
def numPrimeFactorsPairwiseSumProd (A : Finset ℕ) : ℕ :=
  (A.offDiag.val.map (fun p : ℕ × ℕ => p.1 + p.2)).prod.primeFactors.card

/--
Erdős Problem #126 [ErTu34, Er95c, Er97, Er97e]:

Let f(n) be maximal such that if A ⊆ ℕ has |A| = n then ∏_{a ≠ b ∈ A} (a + b)
has at least f(n) distinct prime factors. Is it true that f(n) / log n → ∞?

Erdős and Turán proved that log n ≪ f(n) ≪ n / log n (the upper bound is trivial,
taking A = {1, …, n}).

We state this as: for every constant C > 0, eventually for all n-element sets A ⊆ ℕ,
the product of pairwise sums has at least C · log n distinct prime factors.
-/
theorem erdos_problem_126 :
    ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ A : Finset ℕ, A.card = n →
          (numPrimeFactorsPairwiseSumProd A : ℝ) ≥ C * Real.log n :=
  sorry

end
