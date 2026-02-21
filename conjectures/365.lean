import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

/-- A positive integer n is *powerful* (also called squarefull) if for every
    prime p dividing n, p² also divides n. -/
def IsPowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #365 [Er76d,p.31] [ErGr80,p.68]:

Do all pairs of consecutive powerful numbers n and n+1 come from solutions to
Pell equations? In other words, must either n or n+1 be a square?

Is the number of such n ≤ x bounded by (log x)^{O(1)}?

The first question was answered negatively by Golomb [Go70], who observed that
12167 = 23³ and 12168 = 2³·3²·13² are both powerful (neither is a square).
Walker [Wa76] proved that 7³x² = 3³y² + 1 has infinitely many solutions,
giving infinitely many counterexamples.

The second question remains open. We formalize it: there exists C > 0 such that
for all sufficiently large x, the number of n ≤ x with both n and n+1 powerful
is at most (log x)^C.
-/
theorem erdos_problem_365 :
    ∃ C : ℝ, 0 < C ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 x →
          (∀ n ∈ S, IsPowerful n ∧ IsPowerful (n + 1)) →
          (S.card : ℝ) ≤ (Real.log (x : ℝ)) ^ C :=
  sorry
