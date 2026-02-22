import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

noncomputable section

/-!
# Erdős Problem #683

Is it true that for every $1 \leq k \leq n$ the largest prime divisor of
$\binom{n}{k}$, say $P(\binom{n}{k})$, satisfies
$$P\left(\binom{n}{k}\right) \geq \min(n - k + 1,\; k^{1+c})$$
for some constant $c > 0$?

A problem of Erdős [Er76d][Er79d]. The Sylvester-Schur theorem states that
$P(\binom{n}{k}) > k$ if $k \leq n/2$. Erdős [Er55d] proved that there exists
some $c > 0$ such that $P(\binom{n}{k}) \gg k \log k$ whenever $k \leq n/2$.

https://www.erdosproblems.com/683
-/

/-- The largest prime factor of n, or 1 if n has no prime factors (convention). -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldl max 1

/--
Erdős Problem #683 [Er76d][Er79d]:

There exists a constant c > 0 such that for every 1 ≤ k ≤ n, the largest
prime factor of C(n,k) satisfies P(C(n,k)) ≥ min(n - k + 1, k^{1+c}).

The largest prime factor function returns 1 for n ≤ 1 by convention, which
handles the boundary case k = n where C(n,n) = 1.
-/
theorem erdos_problem_683 :
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      (largestPrimeFactor (Nat.choose n k) : ℝ) ≥
        min (↑(n - k + 1)) ((k : ℝ) ^ (1 + c)) :=
  sorry

end
