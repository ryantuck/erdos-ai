import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #764

Let A ⊆ ℕ. Can there exist some constant c > 0 such that
  ∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n) = cN + O(1)?

Here 1_A ∗ 1_A ∗ 1_A(n) denotes the number of representations of n as
a₁ + a₂ + a₃ with a₁, a₂, a₃ ∈ A (the 3-fold additive convolution).

A conjecture of Erdős [Er65b][Er70c]. Related to [763], which concerns the
2-fold convolution.

DISPROVED: Vaughan [Va72] proved the answer is no in a strong form, showing
that even ∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n) = cN + o(N^{1/4} / (log N)^{1/2})
is impossible. Vaughan's result applies more generally to any h-fold
convolution with different main terms permitted.
-/

/-- The number of representations of `n` as `a₁ + a₂ + a₃` with
    `a₁, a₂, a₃ ∈ A`, i.e., the 3-fold additive convolution
    `1_A ∗ 1_A ∗ 1_A(n)`. -/
noncomputable def repCount764 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 + p.2 ≤ n ∧ p.1 ∈ A ∧ p.2 ∈ A ∧ (n - p.1 - p.2) ∈ A)).card

/-- The partial sum `∑_{n=0}^{N} 1_A ∗ 1_A ∗ 1_A(n)`. -/
noncomputable def repSum764 (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sum (fun n => repCount764 A n)

/--
Erdős Problem #764 (Vaughan's theorem) [Va72]:

For any A ⊆ ℕ and any c > 0, the partial sums ∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n)
cannot satisfy ∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n) = cN + O(1). That is, the error
term |∑_{n ≤ N} 1_A ∗ 1_A ∗ 1_A(n) - cN| is unbounded.
-/
theorem erdos_problem_764 (A : Set ℕ) (c : ℝ) (hc : c > 0) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, |↑(repSum764 A N) - c * ↑N| ≤ C :=
  sorry

end
