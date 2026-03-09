import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open Finset Real

noncomputable section

/--
The number of divisors of n in the open interval (n^{1/2}, n^{1/2} + C·n^{1/4}).
-/
def divisorsInInterval (n : ℕ) (C : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun d =>
    d ∣ n ∧ (Real.sqrt n < (d : ℝ)) ∧ ((d : ℝ) < Real.sqrt n + C * n ^ ((1 : ℝ) / 4))

/--
Erdős Problem #887 [ErRo97]:

Is there an absolute constant K such that, for every C > 0, if n is sufficiently
large then n has at most K divisors in (n^{1/2}, n^{1/2} + C·n^{1/4})?

Erdős and Rosenfeld proved that there are infinitely many n with 4 divisors in
(n^{1/2}, n^{1/2} + n^{1/4}), and ask whether 4 is best possible here.
-/
theorem erdos_problem_887 :
    ∃ K : ℕ, ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (divisorsInInterval n C).card ≤ K :=
  sorry

end
