import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open BigOperators Finset

/--
Erdős Problem #67 — The Erdős Discrepancy Problem
[Er57, Er61, Er64b, Er65b, Er73, Er75b, ErGr79, ErGr80, Er81, Er82e, Er85c, Er90, Er97c]:

If f : ℕ → {-1, +1} then for every C > 0 there exist d, m ≥ 1 such that
|∑_{1 ≤ k ≤ m} f(k * d)| > C.

Proved by Tao (2016), who also proved the more general case when f takes
values on the unit sphere.
-/
theorem erdos_problem_67
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1)
    (C : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∃ m : ℕ, 0 < m ∧
      C < |∑ k ∈ range m, f ((k + 1) * d)| :=
  sorry
