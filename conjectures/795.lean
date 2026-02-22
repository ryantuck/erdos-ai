import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #795

Let g(n) be the maximal size of A ⊆ {1, ..., n} such that the subset products
∏_{a ∈ S} a are distinct for all S ⊆ A. Is it true that

  g(n) ≤ π(n) + π(√n) + o(√n / log n)?

Erdős proved that g(n) ≤ π(n) + O(√n / log n). This upper bound is essentially
best possible, since one could take A to be all primes and squares of primes.

This was solved by Raghavan [Ra25], who proved
  g(n) ≤ π(n) + π(√n) + O(n^{5/12 + o(1)}).
-/

/-- A finset of natural numbers has distinct subset products if for all subsets S, T ⊆ A,
    ∏_{a ∈ S} a = ∏_{a ∈ T} a implies S = T. -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  ∀ S T, S ⊆ A → T ⊆ A → (∏ i ∈ S, i) = (∏ i ∈ T, i) → S = T

/-- The prime counting function π(n): the number of primes ≤ n. -/
def primeCounting (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).card

/-- g(n): the maximal cardinality of A ⊆ {1, ..., n} with distinct subset products. -/
noncomputable def maxDistinctProductSetSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    HasDistinctSubsetProducts A ∧ A.card = k}

/--
Erdős Problem #795:

  g(n) ≤ π(n) + π(⌊√n⌋) + o(√n / log n)

Formulated as: for every ε > 0, there exists N₀ such that for all n ≥ N₀,
  g(n) ≤ π(n) + π(⌊√n⌋) + ε · √n / log n.
-/
theorem erdos_problem_795 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxDistinctProductSetSize n : ℝ) ≤
        (primeCounting n : ℝ) + (primeCounting (Nat.sqrt n) : ℝ) +
        ε * (Nat.sqrt n : ℝ) / Real.log (n : ℝ) :=
  sorry

end
