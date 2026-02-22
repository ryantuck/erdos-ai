import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #820

Let $H(n)$ be the smallest integer $l \geq 2$ such that there exists $k$ with
$2 \leq k < l$ and $\gcd(k^n - 1, l^n - 1) = 1$.

Is it true that $H(n) = 3$ infinitely often? (That is, $\gcd(2^n - 1, 3^n - 1) = 1$
infinitely often?)

Estimate $H(n)$. Is it true that there exists some constant $c > 0$ such that,
for all $\varepsilon > 0$,

  $H(n) > \exp(n^{(c - \varepsilon)/\log\log n})$ for infinitely many $n$

and

  $H(n) < \exp(n^{(c + \varepsilon)/\log\log n})$ for all large enough $n$?

Does a similar upper bound hold for the smallest $k$ such that
$\gcd(k^n - 1, 2^n - 1) = 1$?

The sequence $H(n)$ for $1 \leq n \leq 10$ is $3, 3, 3, 6, 3, 18, 3, 6, 3, 12$.

https://www.erdosproblems.com/820

Tags: number theory
-/

/-- `erdos820_H n` is the smallest integer `l ≥ 2` such that there exists `k` with
    `2 ≤ k < l` and `Nat.Coprime (k ^ n - 1) (l ^ n - 1)`. -/
noncomputable def erdos820_H (n : ℕ) : ℕ :=
  sInf {l : ℕ | 2 ≤ l ∧ ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}

/--
**Erdős Problem #820** — Part 1:

$\gcd(2^n - 1, 3^n - 1) = 1$ for infinitely many $n$.

Equivalently, $H(n) = 3$ for infinitely many $n$.
-/
theorem erdos_820_coprime_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ Nat.Coprime (2 ^ n - 1) (3 ^ n - 1) :=
  sorry

/--
**Erdős Problem #820** — Part 2 (lower bound):

There exists $c > 0$ such that for all $\varepsilon > 0$, for infinitely many $n$,
$H(n) > \exp(n^{(c - \varepsilon)/\log\log n})$.
-/
theorem erdos_820_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    (erdos820_H n : ℝ) >
      Real.exp ((↑n : ℝ) ^ ((c - ε) / Real.log (Real.log (↑n : ℝ)))) :=
  sorry

/--
**Erdős Problem #820** — Part 3 (upper bound):

There exists $c > 0$ such that for all $\varepsilon > 0$, for all sufficiently large $n$,
$H(n) < \exp(n^{(c + \varepsilon)/\log\log n})$.
-/
theorem erdos_820_upper_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    (erdos820_H n : ℝ) <
      Real.exp ((↑n : ℝ) ^ ((c + ε) / Real.log (Real.log (↑n : ℝ)))) :=
  sorry

end
