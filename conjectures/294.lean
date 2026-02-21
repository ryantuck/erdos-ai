import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical Real Finset

/-!
# Erdős Problem #294 (Proved)

Let N ≥ 1 and let t(N) be the least integer t such that there is no solution to
  1 = 1/n₁ + ⋯ + 1/nₖ
with t = n₁ < ⋯ < nₖ ≤ N. Estimate t(N).

Erdős and Graham [ErGr80] showed t(N) ≪ N / log N, but had no idea of the
true value of t(N).

Solved by Liu and Sawhney [LiSa24] (up to (log log N)^{O(1)}), who proved
  N / ((log N)(log log N)³(log log log N)^{O(1)}) ≪ t(N) ≪ N / log N.
-/

/-- There exists a representation of 1 as a sum of distinct unit fractions
    1/n₁ + ⋯ + 1/nₖ with t = n₁ < ⋯ < nₖ ≤ N. Formally: there exists a
    finite set S ⊆ {t, …, N} containing t whose reciprocals sum to 1. -/
def HasUnitFractionRepFrom (t N : ℕ) : Prop :=
  ∃ S : Finset ℕ, t ∈ S ∧ (∀ m ∈ S, t ≤ m) ∧ (∀ m ∈ S, m ≤ N) ∧
    (∀ m ∈ S, 1 ≤ m) ∧ (S.sum fun m => (1 : ℚ) / m) = 1

/-- t(N): the least positive integer t such that there is no unit fraction
    representation of 1 using distinct integers from {t, …, N} starting at t.
    Returns N + 1 as a default if no such t exists. -/
noncomputable def leastNoRep (N : ℕ) : ℕ :=
  if h : ∃ t : ℕ, 1 ≤ t ∧ ¬HasUnitFractionRepFrom t N then
    Nat.find h
  else
    N + 1

/--
Erdős Problem #294 — Upper bound (Erdős–Graham) [ErGr80, p.35]:

There exists a constant C > 0 such that t(N) ≤ C · N / log N for all
sufficiently large N.
-/
theorem erdos_problem_294_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (leastNoRep N : ℝ) ≤ C * (N : ℝ) / Real.log (N : ℝ) :=
  sorry

/--
Erdős Problem #294 — Lower bound (Liu–Sawhney) [LiSa24]:

There exist constants c > 0 and K ≥ 0 such that for all sufficiently large N,
  t(N) ≥ c · N / ((log N) · (log log N)³ · (log log log N)^K).
-/
theorem erdos_problem_294_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) ^ 3 *
        Real.log (Real.log (Real.log (N : ℝ))) ^ K) ≤ (leastNoRep N : ℝ) :=
  sorry
