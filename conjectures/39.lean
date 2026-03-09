import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical
open Finset

/--
A set of natural numbers is a **Sidon set** (or B₂ set) if all pairwise sums
are distinct: for a, b, c, d ∈ A with a ≤ b and c ≤ d,
a + b = c + d implies a = c and b = d.
-/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
The counting function for A up to N: |A ∩ {1, …, N}|.
-/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #39 [Er56, Er61, Er73, Er77c, ErGr80, Er81, Er82e, Er85c, Er91,
Er95, Er97c, Va99]:

Is there an infinite Sidon set A ⊂ ℕ such that
  |A ∩ {1, …, N}| ≫_ε N^{1/2 - ε}
for all ε > 0?

A Sidon set has all pairwise sums distinct. The trivial greedy construction
gives |A ∩ {1,…,N}| ≫ N^{1/3}. The best known bound, due to Ruzsa (1998),
achieves ≫ N^{√2 - 1 + o(1)}. Erdős proved that every infinite Sidon set
satisfies lim inf |A ∩ {1,…,N}| / N^{1/2} = 0, so N^{1/2} is a hard barrier.
-/
theorem erdos_problem_39 :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidonSet A ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ N : ℕ, 0 < N →
            (countingFn A N : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
  sorry
