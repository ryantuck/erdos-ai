import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Filter Topology BigOperators Classical

noncomputable section

/--
The smallest squarefree natural number strictly greater than `n`.
-/
def nextSquarefree (n : ℕ) : ℕ :=
  Nat.find (show ∃ m, m > n ∧ Squarefree m from sorry)

/--
Erdős Problem #145 [Er65b, Er79, Er81h]:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that for any
α ≥ 0 the limit
  lim_{N → ∞} (1/N) · ∑_{squarefree s ≤ N} (nextSquarefree(s) - s)^α
exists?

Erdős proved this for 0 ≤ α ≤ 2; Hooley extended it to α ≤ 3; Greaves–Harman–Huxley
to α ≤ 11/3; and Chan to α ≤ 3.75. Granville showed the full conjecture follows
from the ABC conjecture.
-/
theorem erdos_problem_145 (α : ℝ) (hα : 0 ≤ α) :
    ∃ L : ℝ, Tendsto
      (fun N : ℕ =>
        (↑N)⁻¹ *
          ((Finset.range (N + 1)).filter (fun n => Squarefree n)).sum
            (fun s => ((nextSquarefree s - s : ℕ) : ℝ) ^ α))
      atTop (nhds L) :=
  sorry

end
