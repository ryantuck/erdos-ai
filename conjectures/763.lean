import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #763

Let A ⊆ ℕ. Can there exist some constant c > 0 such that
  ∑_{n ≤ N} 1_A ∗ 1_A(n) = cN + O(1)?

Here 1_A ∗ 1_A(n) denotes the number of representations of n as a + b
with a, b ∈ A.

A conjecture of Erdős and Turán [Er65b][Er70c].

DISPROVED: Erdős and Fuchs [ErFu56] proved the answer is no in a strong
form: even ∑_{n ≤ N} 1_A ∗ 1_A(n) = cN + o(N^{1/4} / (log N)^{1/2})
is impossible. The error term was later improved to o(N^{1/4}) by
Jurkat (unpublished) and Montgomery–Vaughan [MoVa90].
-/

/-- The number of representations of `n` as `a + b` with `a, b ∈ A`,
    i.e., the additive convolution `1_A ∗ 1_A(n)`. -/
noncomputable def repCount763 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/-- The partial sum `∑_{n=0}^{N} 1_A ∗ 1_A(n)`. -/
noncomputable def repSum763 (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sum (fun n => repCount763 A n)

/--
Erdős Problem #763 (Erdős–Fuchs theorem) [ErFu56]:

For any A ⊆ ℕ and any c > 0, the partial sums ∑_{n ≤ N} 1_A ∗ 1_A(n)
cannot satisfy ∑_{n ≤ N} 1_A ∗ 1_A(n) = cN + O(1). That is, the error
term |∑_{n ≤ N} 1_A ∗ 1_A(n) - cN| is unbounded.
-/
theorem erdos_problem_763 (A : Set ℕ) (c : ℝ) (hc : c > 0) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, |↑(repSum763 A N) - c * ↑N| ≤ C :=
  sorry

end
