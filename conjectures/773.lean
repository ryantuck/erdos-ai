import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #773

What is the size of the largest Sidon subset A ⊆ {1², 2², …, N²}? Is it N^{1-o(1)}?

A question of Alon and Erdős [AlEr85], who proved |A| ≥ N^{2/3-o(1)} is possible
(via a random subset), and observed that |A| ≪ N / (log N)^{1/4}, since (as shown
by Landau) the density of the sums of two squares decays like (log N)^{-1/2}.
The lower bound was improved to |A| ≫ N^{2/3} by Lefmann and Thiele [LeTh95].

https://www.erdosproblems.com/773

Tags: number theory, sidon sets, squares
-/

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet773 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The set of perfect squares {1², 2², …, N²}. -/
def squaresUpTo773 (N : ℕ) : Finset ℕ :=
  (Finset.range N).image (fun i => (i + 1) ^ 2)

/--
Erdős Problem #773 (OPEN):

Is the size of the largest Sidon subset of {1², 2², …, N²} equal to N^{1-o(1)}?

That is, for every ε > 0, for all sufficiently large N, there exists a Sidon subset
of {1², 2², …, N²} of size at least N^{1-ε}.

Known bounds:
- Lower: |A| ≫ N^{2/3} (Lefmann–Thiele [LeTh95])
- Upper: |A| ≪ N / (log N)^{1/4} (Alon–Erdős [AlEr85])
-/
theorem erdos_problem_773 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ∃ A : Finset ℕ, A ⊆ squaresUpTo773 N ∧ IsSidonSet773 A ∧
          (A.card : ℝ) ≥ (N : ℝ) ^ (1 - ε) :=
  sorry

end
