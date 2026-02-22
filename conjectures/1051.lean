import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

noncomputable section

/-!
# Erdős Problem #1051

Is it true that if $1 \leq a_1 < a_2 < \cdots$ is a sequence of integers with
  liminf a_n^{1/2^n} > 1
then
  ∑_{n=1}^∞ 1/(a_n · a_{n+1})
is irrational?

This was solved in the affirmative by Aletheia [Fe26]. Extended by Barreto,
Kang, Kim, Kovač, and Zhang [BKKKZ26], who give an essentially complete answer
involving the golden ratio φ = (1 + √5)/2.
-/

/--
Erdős Problem #1051 [ErGr80,p.64] [Er88c,p.106]:

If `a : ℕ → ℕ` is a strictly increasing sequence of positive integers such that
  liminf (a n)^{1/2^n} > 1,
then ∑ n, 1 / (a n * a (n+1)) is irrational.

Proved by Aletheia [Fe26].
-/
theorem erdos_problem_1051 (a : ℕ → ℕ) (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict : StrictMono a)
    (ha_growth : ∃ c : ℝ, c > 1 ∧
      ∀ᶠ n in atTop, (a n : ℝ) ^ ((1 : ℝ) / ((2 : ℝ) ^ (n : ℕ))) ≥ c) :
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry

end
