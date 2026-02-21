import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #224

If $A \subseteq \mathbb{R}^d$ is any set of $2^d + 1$ points then some three
points in $A$ determine an obtuse angle.

## Known results

- For $d = 2$ this is trivial.
- For $d = 3$ there is an unpublished proof by Kuiper and Boerdijk.
- The general case was proved by Danzer and Grünbaum [DaGr62].
-/

/--
Erdős Problem #224 (Danzer–Grünbaum [DaGr62]):
Any set of at least $2^d + 1$ points in $\mathbb{R}^d$ contains three distinct
points $a$, $b$, $c$ such that the angle at $b$ is obtuse
(i.e., $\langle a - b, c - b \rangle < 0$).
-/
theorem erdos_problem_224 (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : 2 ^ d + 1 ≤ A.card) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      @inner ℝ _ _ (a - b) (c - b) < 0 :=
  sorry
