import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
M(n, k) = lcm{n+1, n+2, ..., n+k}, the least common multiple of k consecutive
integers starting from n+1.
-/
def lcmConsecutive (n k : ℕ) : ℕ :=
  (Finset.Icc (n + 1) (n + k)).lcm id

/--
Erdős Problem #677 [Er79, Er79d, ErGr80]:

Let M(n,k) = [n+1, ..., n+k] be the least common multiple of {n+1, ..., n+k}.
Is it true that for all m ≥ n + k, M(n,k) ≠ M(m,k)?

The Thue-Siegel theorem implies that, for fixed k, there are only finitely many
m, n such that m ≥ n + k and M(n,k) = M(m,k).
-/
theorem erdos_problem_677 :
    ∀ n k m : ℕ, 0 < k → m ≥ n + k →
      lcmConsecutive n k ≠ lcmConsecutive m k :=
  sorry
