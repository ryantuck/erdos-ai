import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Filter

/-!
# Erdős Problem #873

Let A = {a₁ < a₂ < ⋯} ⊆ ℕ and let F(A,X,k) count the number of i such that
lcm(aᵢ, aᵢ₊₁, …, aᵢ₊ₖ₋₁) < X. Is it true that, for every ε > 0, there
exists some k such that F(A,X,k) < X^ε?

A problem of Erdős and Szemerédi [Er92c], who proved that for every A,
F(A,X,3) ≪ X^{1/3} log X, and there is an A such that F(A,X,3) ≫ X^{1/3} log X
for infinitely many X.
-/

/-- The lcm of k consecutive terms of a sequence starting at index i. -/
def consecutiveLcm (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

/-- F(a, X, k) counts the number of indices i such that
lcm(a(i), a(i+1), …, a(i+k-1)) < X. We filter over range X since
a strictly increasing implies a(i) ≥ i, so lcm < X forces i < X. -/
def countConsecutiveLcm (a : ℕ → ℕ) (X k : ℕ) : ℕ :=
  ((Finset.range X).filter (fun i => consecutiveLcm a i k < X)).card

/-- Erdős Problem #873 (OPEN):
For any strictly increasing sequence a : ℕ → ℕ of positive integers and any
ε > 0, there exists k such that F(a,X,k) < X^ε for all sufficiently large X. -/
theorem erdos_problem_873 (a : ℕ → ℕ) (ha : StrictMono a) :
    ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, ∀ᶠ X in atTop,
    (countConsecutiveLcm a X k : ℝ) < (X : ℝ) ^ ε :=
  sorry
