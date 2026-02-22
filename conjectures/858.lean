import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #858

Let $A ⊆ \{1, …, N\}$ be such that there is no solution to $at = b$ with
$a, b ∈ A$ and the smallest prime factor of $t$ is $> a$. Estimate the maximum of
$$\frac{1}{\log N} \sum_{n ∈ A} \frac{1}{n}.$$

Alexander [Al66] and Erdős, Sárközi, and Szemerédi [ESS68] proved that this
maximum is $o(1)$ (as $N → ∞$). This condition on $A$ is a weaker form of the
usual primitive condition. If $A$ is primitive then Behrend [Be35] proved
$$\frac{1}{\log N} \sum_{n ∈ A} \frac{1}{n} ≪ \frac{1}{\sqrt{\log \log N}}.$$

An example of such a set $A$ is the set of all integers in $[N^{1/2}, N]$
divisible by some prime $> N^{1/2}$.

https://www.erdosproblems.com/858

Tags: number theory, primitive sets
-/

/-- A finite set A of positive integers satisfies the "weak primitive" condition
    if there do not exist a, b ∈ A with a ∣ b, a < b, and the smallest prime
    factor of b/a is greater than a. Equivalently, whenever at = b for
    a, b ∈ A with t > 1, the smallest prime factor of t is at most a. -/
def WeakPrimitive858 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a < b → a ∣ b →
    Nat.minFac (b / a) ≤ a

/-- The maximum of ∑_{n ∈ A} 1/n over all weak-primitive subsets A ⊆ {1, …, N}. -/
noncomputable def erdos858_maxSum (N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    WeakPrimitive858 A ∧
    x = ∑ n ∈ A, (1 : ℝ) / (n : ℝ)}

/--
**Erdős Problem #858** — Known result [Al66, ESS68]:

The quantity (1/log N) · max{∑_{n ∈ A} 1/n} over weak-primitive subsets
A ⊆ {1, …, N} tends to 0 as N → ∞.

Formulated as: for every ε > 0, there exists N₀ such that for all N ≥ N₀,
  erdos858_maxSum N ≤ ε · log N.
-/
theorem erdos_problem_858 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      erdos858_maxSum N ≤ ε * Real.log (N : ℝ) :=
  sorry

/--
**Erdős Problem #858** — Behrend-type conjecture:

Can we show the stronger bound analogous to Behrend's result for primitive sets?
That is, does there exist C > 0 such that for all sufficiently large N,
  (1/log N) · max{∑_{n ∈ A} 1/n} ≤ C / √(log log N)?
-/
theorem erdos_problem_858_behrend_type :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      erdos858_maxSum N ≤ C * Real.log (N : ℝ) /
        Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  sorry

end
