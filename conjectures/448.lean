import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Classical

noncomputable section

/-!
# Erdős Problem #448

Let $\tau(n)$ count the divisors of $n$ and $\tau^+(n)$ count the number of $k$
such that $n$ has a divisor in $[2^k, 2^{k+1})$. Is it true that, for all
$\epsilon > 0$, $\tau^+(n) < \epsilon \tau(n)$ for almost all $n$?

This was disproved by Erdős and Tenenbaum [ErTe81], who showed that for every
$\epsilon > 0$, the upper density of $\{n : \tau^+(n) \geq \epsilon \tau(n)\}$
is $\asymp \epsilon^{1-o(1)}$ (positive for each fixed $\epsilon$).

Hall and Tenenbaum [HaTe88] showed the upper density is
$\ll \epsilon \log(2/\epsilon)$ and proved that $\tau^+(n)/\tau(n)$ has a
distribution function.
-/

/-- τ⁺(n): the number of k ∈ ℕ such that n has a divisor d with 2^k ≤ d < 2^{k+1}. -/
def tauPlus (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k =>
    (n.divisors.filter (fun d => 2 ^ k ≤ d ∧ d < 2 ^ (k + 1))).Nonempty)).card

/-- Erdős Problem #448 (DISPROVED by Erdős-Tenenbaum [ErTe81]):

For every ε > 0, the upper density of {n : τ⁺(n) ≥ ε · τ(n)} is positive.
This disproves the original conjecture that τ⁺(n) < ε · τ(n) for almost all n. -/
theorem erdos_problem_448 :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        c ≤ ((Finset.Icc 1 N).filter (fun n =>
          (tauPlus n : ℝ) ≥ ε * (n.divisors.card : ℝ))).card / (N : ℝ) :=
  sorry

end
