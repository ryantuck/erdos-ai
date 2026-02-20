import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Filter

/--
For a finite set A ⊆ ℕ, the pair sum product is the product of (a + b)
over all ordered pairs of distinct elements:
  ∏_{a ∈ A} ∏_{b ∈ A \ {a}} (a + b).
This equals ∏_{a ≠ b ∈ A} (a + b) ranging over ordered pairs.
-/
noncomputable def pairSumProduct (A : Finset ℕ) : ℕ :=
  ∏ a ∈ A, ∏ b ∈ A.erase a, (a + b)

/--
The number of distinct prime factors of n (written ω(n) in analytic number theory):
  ω(n) = |{p : p prime, p ∣ n}| = (Nat.primeFactorsList n).toFinset.card.
-/
noncomputable def distinctPrimeFactors (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/--
f(n) is the maximal value such that for every n-element set A ⊆ ℕ,
the product ∏_{a ≠ b ∈ A} (a + b) has at least f(n) distinct prime factors.

Equivalently, f(n) is the minimum over all n-element subsets A ⊆ ℕ
of ω(∏_{a ≠ b ∈ A} (a + b)).
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A.card = n ∧ distinctPrimeFactors (pairSumProduct A) = k}

/--
Erdős Problem #126 (Erdős–Turán [ErTu34]; see also [Er95c, Er97, Er97e]) — OPEN

Let f(n) be maximal such that if A ⊆ ℕ has |A| = n then
∏_{a ≠ b ∈ A} (a + b) has at least f(n) distinct prime factors.
Is it true that f(n) / log n → ∞?

Background: Investigated by Erdős and Turán in their first joint paper [ErTu34],
prompted by a question of Lázár and Grünwald. They proved
  log n ≪ f(n) ≪ n / log n
where the upper bound follows by taking A = {1, ..., n}.
It has never been proved that f(n) = o(n / log n).
-/
theorem erdos_problem_126 :
    Filter.Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) Filter.atTop Filter.atTop :=
  sorry
