import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice

open Finset

noncomputable section

/-- `erdos703_T n r` is the maximum cardinality of a family F of subsets of
    {0, ..., n-1} such that |A ∩ B| ≠ r for all A, B ∈ F. -/
noncomputable def erdos703_T (n r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Finset (Fin n)),
    F.card = k ∧
    ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r}

/--
Erdős Problem #703 (Frankl–Rödl theorem):

Let r ≥ 1 and define T(n,r) to be the maximum size of a family F of subsets
of {1,...,n} such that |A ∩ B| ≠ r for all A, B ∈ F.

For every ε > 0 there exists δ > 0 such that for all n and r with
εn < r < (1/2 - ε)n, we have T(n,r) < (2 - δ)^n.

Proved by Frankl and Rödl [FrRo87].

https://www.erdosproblems.com/703
-/
theorem erdos_problem_703 :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
      ∀ n : ℕ, ∀ r : ℕ,
        ε * (n : ℝ) < (r : ℝ) →
        (r : ℝ) < (1 / 2 - ε) * (n : ℝ) →
        (erdos703_T n r : ℝ) < (2 - δ) ^ n :=
  sorry

end
