import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Finset.Defs

/-!
# Erdős Problem #969

Let Q(x) count the number of squarefree integers in [1,x]. Determine the order of magnitude
in the error term in the asymptotic Q(x) = (6/π²)x + E(x).

It is elementary that E(x) ≪ x^{1/2}, and the prime number theorem gives o(x^{1/2}).
Evelyn and Linfoot proved E(x) = Ω(x^{1/4}), and this is likely the true order of magnitude.
The Riemann Hypothesis would follow from E(x) = O(x^{1/4}).

The conjecture is that for every ε > 0, there exists C > 0 such that for all sufficiently
large x, |E(x)| ≤ C · x^{1/4 + ε}.
-/

noncomputable section

open Finset Real

/-- The number of squarefree positive integers in [1, x]. -/
def squarefreeCount (x : ℕ) : ℕ :=
  ((Icc 1 x).filter Squarefree).card

/-- The error term E(x) = Q(x) - (6/π²)x in the squarefree counting asymptotic. -/
def squarefreeError (x : ℕ) : ℝ :=
  (squarefreeCount x : ℝ) - (6 / Real.pi ^ 2) * (x : ℝ)

/--
Erdős Problem #969:

The error term E(x) in the squarefree counting function Q(x) = (6/π²)x + E(x)
satisfies E(x) = O(x^{1/4 + ε}) for every ε > 0. Combined with the known lower
bound E(x) = Ω(x^{1/4}) of Evelyn and Linfoot, this would establish that x^{1/4}
is the true order of magnitude of E(x).

Formalized as: for every ε > 0, there exists C > 0 and x₀ such that for all
x ≥ x₀, |E(x)| ≤ C · x^{1/4 + ε}.
-/
theorem erdos_problem_969 (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      |squarefreeError x| ≤ C * (x : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry

end
