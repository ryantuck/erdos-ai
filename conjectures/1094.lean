import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat

namespace Erdos1094

/--
Erdős Problem #1094 (OPEN) [ELS88][ELS93]:

For all n ≥ 2k, the least prime factor of C(n, k) is ≤ max(n/k, k),
with only finitely many exceptions.

The 14 known exceptions are explicitly listed in [ELS88]:
C(7,3), C(13,4), C(23,5), C(14,4), C(44,8), C(46,10), C(47,10),
C(47,11), C(62,6), C(74,10), C(94,10), C(95,10), C(241,16), C(284,28).
-/
theorem erdos_problem_1094 :
    Set.Finite {p : ℕ × ℕ |
      let n := p.1
      let k := p.2
      1 ≤ k ∧ 2 * k ≤ n ∧
      ¬(Nat.choose n k).minFac ≤ max (n / k) k} :=
  sorry

end Erdos1094
