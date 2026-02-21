import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Classical

noncomputable section

/-!
# Erdős Problem #449

Let $r(n)$ count the number of pairs $(d_1, d_2)$ such that $d_1 \mid n$ and
$d_2 \mid n$ and $d_1 < d_2 < 2d_1$. Is it true that, for every $\epsilon > 0$,
$r(n) < \epsilon \tau(n)$ for almost all $n$, where $\tau(n)$ is the number of
divisors of $n$?

This is false. For any constant $K > 0$, we have $r(n) > K\tau(n)$ for a
positive density set of $n$. Kevin Ford observed this follows from the negative
solution to [448] via the Cauchy–Schwarz inequality.
-/

/-- r(n): the number of ordered pairs (d₁, d₂) of divisors of n with d₁ < d₂ < 2·d₁. -/
def closeDivisorPairs (n : ℕ) : ℕ :=
  ((n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2 ∧ p.2 < 2 * p.1)).card

/-- Erdős Problem #449 (DISPROVED by Ford, via the negative solution to [448]):

For every K > 0, the upper density of {n : r(n) ≥ K · τ(n)} is positive.
This disproves the original conjecture that r(n) < ε · τ(n) for almost all n. -/
theorem erdos_problem_449 :
    ∀ K : ℝ, K > 0 →
    ∃ c : ℝ, c > 0 ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        c ≤ ((Finset.Icc 1 N).filter (fun n =>
          (closeDivisorPairs n : ℝ) ≥ K * (n.divisors.card : ℝ))).card / (N : ℝ) :=
  sorry

end
