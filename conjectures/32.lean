import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card

open Real Set

/--
A set A ⊆ ℕ is an **additive complement to the primes** if every sufficiently
large natural number can be written as p + a for some prime p and some a ∈ A.
-/
def IsAdditiveComplement (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ p : ℕ, Nat.Prime p ∧ ∃ a ∈ A, n = p + a

/--
The counting function of A up to N: |A ∩ {1, …, N}|.
-/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 N).ncard

/--
Erdős Problem #32 [Er56, Er57, Er59, Er61, Er65b, Er73, Er77c]:

Is there a set A ⊂ ℕ such that |A ∩ {1,…,N}| = o((log N)²) and every
sufficiently large integer can be written as p + a for some prime p and a ∈ A?

Erdős proved that such a set exists with |A ∩ {1,…,N}| ≪ (log N)².
The question is whether the (log N)² bound can be improved.
-/
theorem erdos_problem_32a :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countingFn A N : ℝ) ≤ ε * (Real.log N) ^ 2 :=
  sorry

/--
Erdős Problem #32, second part:

Can one find an additive complement A to the primes with
|A ∩ {1,…,N}| = O(log N)?

Erdős offered $50 for determining whether this is possible.
-/
theorem erdos_problem_32b :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        (countingFn A N : ℝ) ≤ C * Real.log N :=
  sorry
