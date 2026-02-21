import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #460

Let $a_0 = 0$ and $a_1 = 1$, and in general define $a_k$ to be the least
integer $> a_{k-1}$ for which $\gcd(n - a_k, n - a_i) = 1$ for all
$0 \leq i < k$. Does
$$\sum_{0 < a_i < n} \frac{1}{a_i} \to \infty$$
as $n \to \infty$?

This problem arose in work of Eggleton, Erdős, and Selfridge.
-/

/-- The greedy coprime-complement sequence for a given `n`.
    `erdos460_seq n 0 = 0` and `erdos460_seq n (k+1)` is the least integer
    greater than `erdos460_seq n k` such that `n - erdos460_seq n (k+1)` is
    coprime to `n - erdos460_seq n i` for all `i ≤ k`. -/
noncomputable def erdos460_seq (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sInf {m : ℕ | erdos460_seq n k < m ∧
      ∀ i : ℕ, i ≤ k → Nat.Coprime (n - m) (n - erdos460_seq n i)}

/-- The sum $\sum_{0 < a_i < n} 1/a_i$ for the greedy coprime-complement
    sequence. Since the sequence is strictly increasing with
    `erdos460_seq n 0 = 0`, all relevant indices satisfy `k < n`. -/
noncomputable def erdos460_sum (n : ℕ) : ℝ :=
  ((Finset.range n).filter (fun k =>
    0 < erdos460_seq n k ∧ erdos460_seq n k < n)).sum
    (fun k => (1 : ℝ) / (erdos460_seq n k : ℝ))

/--
Erdős Problem #460 [Er77c, p.64]:

Does $\sum_{0 < a_i < n} 1/a_i \to \infty$ as $n \to \infty$, where
$(a_k)$ is the greedy sequence with $a_0 = 0$ and each $a_{k+1}$ the least
integer greater than $a_k$ making $\gcd(n - a_{k+1}, n - a_i) = 1$ for all
$i \leq k$?
-/
theorem erdos_problem_460 :
    Tendsto erdos460_sum atTop atTop :=
  sorry

end
