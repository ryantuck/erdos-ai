import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Nat Finset

namespace Erdos396

/--
Erdős Problem #396 [ErGr80]:

Is it true that for every k there exists n such that
  ∏_{0 ≤ i ≤ k} (n - i) ∣ C(2n, n)?

Erdős and Graham note that (n+1) ∣ C(2n, n) always holds (giving Catalan numbers),
but it is quite rare for n ∣ C(2n, n).
-/
theorem erdos_problem_396 :
    ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧
      (∏ i ∈ range (k + 1), (n - i)) ∣ (2 * n).choose n :=
  sorry

end Erdos396
