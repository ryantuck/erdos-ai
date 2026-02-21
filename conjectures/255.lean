import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset Classical

/--
The discrepancy of a sequence z : ℕ → ℝ at length N with respect to
a sub-interval [a, b] ⊆ [0, 1]:
  D_N([a,b]) = #{n < N : z(n) ∈ [a, b]} - N * (b - a)
-/
noncomputable def discrepancy (z : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (((range N).filter (fun n => a ≤ z n ∧ z n ≤ b)).card : ℝ) - (N : ℝ) * (b - a)

/--
Erdős Problem #255 (proved by Schmidt [Sc68]):

Let z₁, z₂, … ∈ [0,1] be an infinite sequence. Define the discrepancy
  D_N(I) = #{n ≤ N : zₙ ∈ I} - N·|I|.
Then there must exist some interval I ⊆ [0,1] such that
  limsup_{N → ∞} |D_N(I)| = ∞.

Equivalently: for any sequence in [0,1], there exists a sub-interval
[a,b] ⊆ [0,1] such that |D_N([a,b])| is unbounded as N → ∞.
-/
theorem erdos_problem_255 :
    ∀ z : ℕ → ℝ,
    (∀ n, 0 ≤ z n ∧ z n ≤ 1) →
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      ∀ M : ℝ, ∃ N : ℕ, |discrepancy z a b N| ≥ M :=
  sorry
