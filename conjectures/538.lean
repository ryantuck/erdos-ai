import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real

noncomputable section

/-!
# Erdős Problem #538

Let $r \geq 2$ and suppose that $A \subseteq \{1, \ldots, N\}$ is such that, for
any $m$, there are at most $r$ solutions to $m = pa$ where $p$ is prime and
$a \in A$. Give the best possible upper bound for $\sum_{n \in A} 1/n$.

Erdős observed that
$$\sum_{n \in A} \frac{1}{n} \sum_{p \leq N} \frac{1}{p}
  \leq r \sum_{m \leq N^2} \frac{1}{m} \ll r \log N,$$
and hence
$$\sum_{n \in A} \frac{1}{n} \ll r \frac{\log N}{\log \log N}.$$

The problem asks whether this bound is the best possible.
-/

/-- The number of representations of `m` as `p * a` where `p` is prime and
`a ∈ A`. Since `p` is determined by `a` (as `p = m / a`), this counts
elements `a ∈ A` with `a ∣ m` and `m / a` prime. -/
def numPrimeProductReps (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => a ∣ m ∧ Nat.Prime (m / a))).card

/--
**Erdős Problem #538** (Erdős's upper bound):

There exists a constant `C > 0` such that for all `r ≥ 2` and sufficiently
large `N`, if `A ⊆ {1, …, N}` has at most `r` representations `m = p * a`
(with `p` prime and `a ∈ A`) for every `m`, then
$$\sum_{n \in A} \frac{1}{n} \leq C \cdot r \cdot \frac{\log N}{\log \log N}.$$
-/
theorem erdos_problem_538_upper :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ r : ℕ, 2 ≤ r →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N →
        (∀ m : ℕ, numPrimeProductReps A m ≤ r) →
        A.sum (fun n => (1 : ℝ) / (n : ℝ)) ≤
          C * (r : ℝ) * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) :=
  sorry

/--
**Erdős Problem #538** (Sharpness conjecture):

The upper bound is best possible: there exists `c > 0` such that for all
`r ≥ 2` and sufficiently large `N`, there exists `A ⊆ {1, …, N}` satisfying
the representation constraint with
$$\sum_{n \in A} \frac{1}{n} \geq c \cdot r \cdot \frac{\log N}{\log \log N}.$$
-/
theorem erdos_problem_538_lower :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ r : ℕ, 2 ≤ r →
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ m : ℕ, numPrimeProductReps A m ≤ r) ∧
        c * (r : ℝ) * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ≤
          A.sum (fun n => (1 : ℝ) / (n : ℝ)) :=
  sorry

end
