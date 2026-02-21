import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

noncomputable section

/-- A positive integer n has the Erdős-261 property if n/2^n can be written as
    a finite sum ∑_{a ∈ S} a/2^a for some set S of at least 2 distinct positive
    integers. -/
def HasErdos261Property (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, 2 ≤ S.card ∧ (∀ a ∈ S, 0 < a) ∧
    (n : ℝ) / (2 : ℝ) ^ n = ∑ a ∈ S, (a : ℝ) / (2 : ℝ) ^ a

/--
Erdős Problem #261, Part 1 [Er74b, ErGr80, Er88c]:
Are there infinitely many n such that there exists some t ≥ 2 and distinct
integers a₁, ..., aₜ ≥ 1 such that n/2^n = ∑_{k≤t} aₖ/2^{aₖ}?
-/
theorem erdos_problem_261_part1 :
    Set.Infinite {n : ℕ | HasErdos261Property n} :=
  sorry

/--
Erdős Problem #261, Part 2 [Er74b, ErGr80, Er88c]:
Is it true for all positive integers n that n/2^n can be written as a finite
sum of at least 2 distinct terms a/2^a?
-/
theorem erdos_problem_261_part2 :
    ∀ n : ℕ, 0 < n → HasErdos261Property n :=
  sorry

/--
Erdős Problem #261, Part 3 [Er74b, ErGr80, Er88c]:
Is there a rational x such that x = ∑_{k=1}^∞ aₖ/2^{aₖ} has at least
2^ℵ₀ solutions, where the aₖ form a strictly increasing sequence of
positive integers?
-/
theorem erdos_problem_261_part3 :
    ∃ x : ℝ, (∃ q : ℚ, x = (q : ℝ)) ∧
      ¬ Set.Countable {a : ℕ → ℕ | StrictMono a ∧ (∀ n, 0 < a n) ∧
        HasSum (fun n => (a n : ℝ) / (2 : ℝ) ^ (a n)) x} :=
  sorry

end
