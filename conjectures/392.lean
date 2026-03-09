import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Filter

noncomputable section

/--
For n : ℕ, the minimum number of factors t such that n! = a₁ · ... · aₜ
with 1 ≤ aᵢ ≤ n² for all i.
-/
noncomputable def erdos392_A (n : ℕ) : ℕ :=
  sInf {t : ℕ | ∃ l : List ℕ, l.length = t ∧
    (∀ x ∈ l, 1 ≤ x ∧ x ≤ n ^ 2) ∧ l.prod = n.factorial}

/--
Erdős Problem #392 [ErGr80, p.75] (PROVED):

Let A(n) denote the least value of t such that n! = a₁ · ... · aₜ
with a₁ ≤ ... ≤ aₜ ≤ n². Is it true that
  A(n) = n/2 − n/(2 log n) + o(n/log n)?

Cambie observed that a positive answer follows from the known result for
the variant with aₜ ≤ n (whose asymptotics are n − n/log n + o(n/log n)
via a greedy decomposition), simply by pairing factors together.
The lower bound follows from Stirling's approximation.
-/
theorem erdos_problem_392 :
    Tendsto (fun n : ℕ =>
      ((erdos392_A n : ℝ) - (n : ℝ) / 2 + (n : ℝ) / (2 * Real.log (n : ℝ))) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds 0) :=
  sorry

end
