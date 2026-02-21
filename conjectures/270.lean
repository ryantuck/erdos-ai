import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Finset BigOperators

/--
Erdős Problem #270 [ErGr80, p.66] (Disproved):

Let f(n) → ∞ as n → ∞. Is it true that
  ∑_{n ≥ 1} 1/((n+1)⋯(n+f(n)))
is irrational?

Disproved by Crmarić and Kovač [CrKo25]: for any α ∈ (0, ∞) there exists
f : ℕ → ℕ such that f(n) → ∞ and the sum equals α. In particular, choosing
α rational gives a counterexample to the original conjecture.
-/
theorem erdos_problem_270
    (α : ℝ) (hα : 0 < α) :
    ∃ f : ℕ → ℕ,
      Tendsto f atTop atTop ∧
      HasSum (fun n => (1 : ℝ) / (∏ i ∈ Finset.range (f (n + 1)),
        ((n : ℝ) + 2 + (i : ℝ)))) α :=
  sorry
