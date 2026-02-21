import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #450

How large must y = y(ε, n) be such that the number of integers in (x, x+y) with a
divisor in (n, 2n) is at most ε·y?

The intended quantifier on x is not entirely clear from the original source. We formalize
the "for all x" interpretation: for every ε > 0 and n ≥ 1, there exists y such that
for all x, the count of integers in (x, x+y) with a divisor in (n, 2n) is at most ε·y.

Cambie observed that the "for all x" version fails when
ε·(log n)^δ·(log log n)^{3/2} → ∞ (using results of Ford [Fo08]), so this formalization
may require additional conditions on ε and n.
-/

/-- Count of integers in the open interval (x, x + y) having at least one divisor
    in the open interval (n, 2n). -/
def countWithDivisorInRange (x y n : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (fun m =>
    ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m)).card

/--
Erdős Problem #450 [ErGr80, p.89]:

For every ε > 0 and n ≥ 1, there exists y such that for all x, the number of integers
in (x, x + y) with a divisor in (n, 2n) is at most ε · y.
-/
theorem erdos_problem_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : ℕ, 0 < y ∧ ∀ x : ℕ,
      (countWithDivisorInRange x y n : ℝ) ≤ ε * (y : ℝ) :=
  sorry

end
