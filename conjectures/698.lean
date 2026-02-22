import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős Problem #698

Is there some $h(n) \to \infty$ such that for all $2 \leq i < j \leq n/2$,
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \geq h(n)?$$

A problem of Erdős and Szekeres [ErSz78], who observed that
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \geq \frac{\binom{n}{i}}{\binom{j}{i}} \geq 2^i$$
(in particular the greatest common divisor is always > 1). This inequality is
sharp for i = 1, j = p, and n = 2p.

Resolved by Bergman [Be11], who proved that for any 2 ≤ i < j ≤ n/2,
$$\gcd\left(\binom{n}{i}, \binom{n}{j}\right) \gg n^{1/2} \cdot 2^i / i^{3/2},$$
where the implied constant is absolute.

https://www.erdosproblems.com/698
-/

/--
Erdős Problem #698 [ErSz78] — PROVED by Bergman [Be11]:

There exists h : ℕ → ℕ with h(n) → ∞ such that for all 2 ≤ i < j ≤ n/2,
  gcd(C(n,i), C(n,j)) ≥ h(n).
-/
theorem erdos_problem_698 :
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
    ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      h n ≤ Nat.gcd (Nat.choose n i) (Nat.choose n j) :=
  sorry
