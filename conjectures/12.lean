import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped Classical
open Finset BigOperators

/--
A set A ⊆ ℕ is *sum-divisibility-free* if there are no distinct a, b, c ∈ A
with b, c > a and a ∣ (b + c).
-/
def SumDivFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c →
    a < b → a < c → ¬(a ∣ (b + c))

/-- Counting function: |A ∩ {1, …, N}|. -/
noncomputable def counting (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #12, Part 1 [ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97]:

Let A be an infinite set such that there are no distinct a, b, c ∈ A with
a ∣ (b + c) and b, c > a. Is there such an A with
  lim inf_{N→∞} |A ∩ {1,…,N}| / √N > 0 ?
-/
theorem erdos_problem_12a :
    ∃ A : Set ℕ, A.Infinite ∧ SumDivFree A ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ε ≤ (counting A N : ℝ) / Real.sqrt (N : ℝ) :=
  sorry

/--
Erdős Problem #12, Part 2 [ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97]:

Does there exist an absolute constant c > 0 such that for every infinite
sum-divisibility-free set A, there are infinitely many N with
  |A ∩ {1,…,N}| < N^{1-c} ?
-/
theorem erdos_problem_12b :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : Set ℕ, A.Infinite → SumDivFree A →
        ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
          (counting A N : ℝ) < (N : ℝ) ^ ((1 : ℝ) - c) :=
  sorry

/--
Erdős Problem #12, Part 3 [ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97]:

For every infinite sum-divisibility-free set A, is it true that
  ∑_{n ∈ A} 1/n < ∞ ?
-/
theorem erdos_problem_12c
    (A : Set ℕ)
    (hInf : A.Infinite)
    (hA : SumDivFree A) :
    ∃ M : ℝ, ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ A →
      ∑ n ∈ F, (1 : ℝ) / (n : ℝ) ≤ M :=
  sorry
