import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

noncomputable section

/-!
# Erdős Problem #665

A pairwise balanced design for {1,...,n} is a collection of sets A₁,...,Aₘ ⊆ {1,...,n}
such that 2 ≤ |Aᵢ| < n and every pair of distinct elements x,y ∈ {1,...,n} is contained
in exactly one Aᵢ.

Is there a constant C > 0 and, for all large n, a pairwise balanced design such that
|Aᵢ| > n^{1/2} - C for all 1 ≤ i ≤ m?

A problem of Erdős and Larson [ErLa82]. Shrikhande and Singhi [ShSi85] proved that
the answer is no conditional on the conjecture that the order of every projective
plane is a prime power.
-/

/-- A pairwise balanced design on `Fin n`: a family of blocks where each block has
    at least 2 and fewer than n elements, and every pair of distinct elements is
    contained in exactly one block. -/
def IsPairwiseBalancedDesign665 (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, 2 ≤ B.card ∧ B.card < n) ∧
  (∀ x y : Fin n, x ≠ y → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B)

/--
Erdős Problem #665 [ErLa82][Er97f]:

Is there a constant C > 0 such that for all sufficiently large n, there exists
a pairwise balanced design on {1,...,n} where every block has size > √n - C?
-/
theorem erdos_problem_665 :
    ∃ C : ℝ, C > 0 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∃ blocks : Finset (Finset (Fin n)),
      IsPairwiseBalancedDesign665 n blocks ∧
      ∀ B ∈ blocks, (↑B.card : ℝ) > Real.sqrt ↑n - C :=
  sorry

end
