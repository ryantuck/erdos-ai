import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset Nat

/--
Erdős Problem #377 [EGRS75, Er79, ErGr80]:

Is there some absolute constant $C > 0$ such that
$$\sum_{\substack{p \leq n \\ p \nmid \binom{2n}{n}}} \frac{1}{p} \leq C$$
for all $n$ (where the summation is restricted to primes $p \leq n$)?

A question of Erdős, Graham, Ruzsa, and Straus, who proved that the average
value of the sum converges to $\gamma_0 = \sum_{k=2}^{\infty} \frac{\log k}{2^k}$,
so that for almost all integers the sum is $\gamma_0 + o(1)$.
-/
theorem erdos_problem_377 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 0 < n →
        (((Finset.filter (fun p =>
            Nat.Prime p ∧ p ≤ n ∧ ¬(p ∣ Nat.choose (2 * n) n))
            (Finset.range (n + 1))).sum
          (fun p => (1 : ℝ) / p)) ≤ C) :=
  sorry
