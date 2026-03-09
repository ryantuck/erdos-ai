import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Interval

open Finset

/--
Given sets A and B of integers and an integer x, the number of
pairs (a, b) with a ∈ A, b ∈ B, and a - b = x.
-/
noncomputable def repCount (A B : Finset ℤ) (x : ℤ) : ℕ :=
  (A.filter fun a => (a - x) ∈ B).card

/--
Erdős Problem #36 [Er55, Er56, Er61, Er92c] — The Minimum Overlap Problem:

Find the optimal constant c > 0 such that for all sufficiently large N, if
A ⊔ B = {1,…,2N} is a partition into two equal parts (|A| = |B| = N), then
there exists some x such that the number of solutions to a - b = x with
a ∈ A and b ∈ B is at least cN.

The example A = {N/2+1,…,3N/2} shows c ≤ 1/2. The current best bounds are
0.379005 < c < 0.380876.
-/
theorem erdos_problem_36 :
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A B : Finset ℤ),
          A ∪ B = Finset.Icc (1 : ℤ) (2 * ↑N) →
          Disjoint A B →
          A.card = N →
          B.card = N →
          ∃ x : ℤ, (repCount A B x : ℝ) ≥ c * (N : ℝ) :=
  sorry
