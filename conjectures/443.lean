import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real

/-!
# Erdős Problem #443

Let $m,n\geq 1$. What is
$\# \{ k(m-k) : 1\leq k\leq m/2\} \cap \{ l(n-l) : 1\leq l\leq n/2\}$?
Can it be arbitrarily large? Is it $\leq (mn)^{o(1)}$ for all sufficiently
large $m,n$?

This was solved independently by Hegyvári [He25] and Cambie (unpublished), who
show that if $m > n$ then the set in question has size
$\leq m^{O(1/\log\log m)}$, and that for any integer $s$ there exist infinitely
many pairs $(m,n)$ such that the set in question has size $s$.
-/

/-- The set {k(m-k) : 1 ≤ k ≤ m/2} of products arising from partitioning m
    into two positive parts k and m-k with k ≤ m/2. -/
def productSet (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (m / 2)).image (fun k => k * (m - k))

/-- The number of common values in the product sets for m and n. -/
def commonProducts (m n : ℕ) : ℕ :=
  ((productSet m) ∩ (productSet n)).card

/-- Erdős Problem #443, part 1 (PROVED):
The intersection can be arbitrarily large. For any s, there exist
arbitrarily large m and some n ≥ 1 with |productSet m ∩ productSet n| ≥ s.

Proved independently by Hegyvári [He25] and Cambie (unpublished). -/
theorem erdos_problem_443_arbitrarily_large (s : ℕ) :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∃ n : ℕ, 1 ≤ n ∧ s ≤ commonProducts m n :=
  sorry

/-- Erdős Problem #443, part 2 (PROVED):
If m > n then the intersection has subpolynomial size:
|productSet m ∩ productSet n| ≤ m^{C / log log m} for some constant C > 0
and all sufficiently large m.

Proved independently by Hegyvári [He25] and Cambie (unpublished). -/
theorem erdos_problem_443_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∀ n : ℕ, 1 ≤ n → n < m →
    (commonProducts m n : ℝ) ≤ (m : ℝ) ^ (C / Real.log (Real.log (m : ℝ))) :=
  sorry
