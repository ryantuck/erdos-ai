import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Finset

/--
Erdős Problem #702 (Erdős–Sós Conjecture):

Let k ≥ 4. If F is a family of subsets of {1,…,n} with |A| = k for all A ∈ F
and |F| > C(n-2, k-2), then there are A, B ∈ F such that |A ∩ B| = 1.

Proved by Katona (unpublished) for k = 4, and by Frankl [Fr77] for all k ≥ 4.

https://www.erdosproblems.com/702
-/
theorem erdos_problem_702 (n k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n)
    (F : Finset (Finset (Fin n)))
    (hF_unif : ∀ A ∈ F, A.card = k)
    (hF_large : F.card > Nat.choose (n - 2) (k - 2)) :
    ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ (A ∩ B).card = 1 :=
  sorry
