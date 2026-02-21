import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/--
Erdős Problem #362 (Part 1):
Let A ⊆ ℕ be a finite set of size N. For any fixed t, the number of
subsets S ⊆ A with ∑_{n ∈ S} n = t is ≪ 2^N / N^{3/2}.

Proved by Sárközy and Szemerédi, removing a log factor from the earlier
bound of Erdős and Moser.
-/
theorem erdos_problem_362a :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t : ℕ),
    ((A.powerset.filter (fun S => decide (S.sum id = t))).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ ((3 : ℝ) / 2)) :=
  sorry

/--
Erdős Problem #362 (Part 2):
Let A ⊆ ℕ be a finite set of size N. For any fixed t and l, the number of
subsets S ⊆ A with ∑_{n ∈ S} n = t and |S| = l is ≪ 2^N / N^2,
with the implied constant independent of l and t.

Proved by Halász as a consequence of a more general multi-dimensional result.
-/
theorem erdos_problem_362b :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset ℕ), A.card = N →
    ∀ (t l : ℕ),
    ((A.powerset.filter (fun S => decide (S.sum id = t ∧ S.card = l))).card : ℝ) ≤
      C * (2 : ℝ) ^ N / ((N : ℝ) ^ 2) :=
  sorry
