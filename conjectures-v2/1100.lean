/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1100

*Reference:* [erdosproblems.com/1100](https://www.erdosproblems.com/1100)

[ErHa78] Erdős, P. and Hall, R. R., _On some unconventional problems on the divisors of
integers_. J. Austral. Math. Soc. Ser. A (1978), 479–485.

[Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_.
Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.

If $1 = d_1 < \cdots < d_{\tau(n)} = n$ are the divisors of $n$, let $\tau^\perp(n)$ count the
number of $i$ for which $\gcd(d_i, d_{i+1}) = 1$.

Part 1: Is it true that $\tau^\perp(n)/\omega(n) \to \infty$ for almost all $n$?

Part 2: Is it true that $\tau^\perp(n) < \exp((\log n)^{o(1)})$ for all $n$?
Equivalently, for every $\varepsilon > 0$ and sufficiently large $n$,
$\tau^\perp(n) < \exp((\log n)^\varepsilon)$.

Part 3: Let $g(k) = \max$ over squarefree $n$ with $\omega(n) = k$ of $\tau^\perp(n)$.
Determine the growth of $g(k)$. Erdős and Simonovits proved
$(\sqrt{2} + o(1))^k < g(k) < (2 - c)^k$ for some constant $c > 0$ (see [Er81h, p.173]).

The problem is listed as OPEN on the source page (page last edited 19 October 2025,
accessed 2026-02-23). The function $\tau^\perp$ was considered by Erdős and Hall [ErHa78].
It is trivial that $\tau^\perp(n) \ge \omega(n)$, with equality for infinitely many $n$
(e.g. prime powers). Erdős and Hall [ErHa78] proved that for all $\epsilon > 0$ and
sufficiently large $x$, $\max_{n < x} \tau^\perp(n) > \exp((\log\log x)^{2-\epsilon})$;
these two results are formalized as variants below.

Related OEIS sequence: [A325864](https://oeis.org/A325864) (marked "possible" on the page).
-/

open Finset Real

namespace Erdos1100

/-- The sorted list of divisors of $n$ in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- $\tau^\perp(n)$: the number of indices $i$ such that $\gcd(d_i, d_{i+1}) = 1$,
where $d_1 < \cdots < d_{\tau(n)}$ are the divisors of $n$ in increasing order. -/
def tauPerp (n : ℕ) : ℕ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).filter (fun p => Nat.gcd p.1 p.2 == 1)).length

/--
Erdős Problem 1100, Part 1:
Is it true that $\tau^\perp(n)/\omega(n) \to \infty$ for almost all $n$? That is, for every
bound $M$, the natural density of $\{n : \tau^\perp(n) \le M \cdot \omega(n)\}$ is zero.
-/
@[category research open, AMS 11]
theorem erdos_1100 :
    answer(sorry) ↔
      ∀ M : ℕ, ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (((range N).filter (fun n =>
            tauPerp n ≤ M * n.primeFactors.card)).card : ℝ) / (N : ℝ) < ε := by
  sorry

/--
Erdős Problem 1100, Part 2:
Is it true that for every $\varepsilon > 0$, for all sufficiently large $n$,
$\tau^\perp(n) < \exp((\log n)^\varepsilon)$?
This formalizes the conjecture that $\tau^\perp(n) < \exp((\log n)^{o(1)})$.
-/
@[category research open, AMS 11]
theorem erdos_1100.variants.part2 :
    answer(sorry) ↔
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          (tauPerp n : ℝ) < exp ((log (n : ℝ)) ^ ε) := by
  sorry

/--
Erdős Problem 1100, Part 3 (upper bound, proved by Erdős–Simonovits):
There exists $c > 0$ such that for all sufficiently large $k$, every squarefree $n$
with $\omega(n) = k$ satisfies $\tau^\perp(n) < (2 - c)^k$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.part3_upper :
    ∃ c : ℝ, c > 0 ∧
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∀ n : ℕ, Squarefree n → n.primeFactors.card = k →
          (tauPerp n : ℝ) < (2 - c) ^ k := by
  sorry

/--
Erdős Problem 1100, Part 3 (lower bound, proved by Erdős–Simonovits):
For every $0 < \varepsilon < \sqrt{2}$ and sufficiently large $k$, there exists a
squarefree $n$ with $\omega(n) = k$ and $\tau^\perp(n) > (\sqrt{2} - \varepsilon)^k$.

The restriction $\varepsilon < \sqrt{2}$ keeps the base $\sqrt{2} - \varepsilon$
nonnegative and is necessary: without it the statement is false, since for
$\varepsilon > 2 + \sqrt{2}$ and even $k$ the (monoid-power) bound
$(\sqrt{2} - \varepsilon)^k = (\varepsilon - \sqrt{2})^k > 2^k$ exceeds the trivial
maximum $\tau^\perp(n) \le \tau(n) - 1 = 2^k - 1$ for squarefree $n$ with
$\omega(n) = k$. For $\varepsilon \ge \sqrt{2}$ the informal statement carries no
content, so nothing is lost.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.part3_lower :
    ∀ ε : ℝ, ε > 0 → ε < sqrt 2 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∃ n : ℕ, Squarefree n ∧ n.primeFactors.card = k ∧
          (tauPerp n : ℝ) > (sqrt 2 - ε) ^ k := by
  sorry

/--
Erdős Problem 1100, variant (trivial bound, remark in [ErHa78]):
$\tau^\perp(n) \ge \omega(n)$ for every $n$. Indeed, for each prime $p \mid n$ the
immediate predecessor $d$ of $p$ in the sorted divisor list satisfies $d < p$, hence
$\gcd(d, p) = 1$, giving $\omega(n)$ distinct coprime consecutive pairs.
(For $n = 0$ and $n = 1$ both sides are $0$.)
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.omega_lower_bound :
    ∀ n : ℕ, n.primeFactors.card ≤ tauPerp n := by
  sorry

/--
Erdős Problem 1100, variant (remark in [ErHa78]):
$\tau^\perp(n) = \omega(n)$ for infinitely many $n$ — e.g. for prime powers $p^a$,
where the only coprime consecutive divisor pair is $(1, p)$, so
$\tau^\perp(p^a) = 1 = \omega(p^a)$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.omega_equality_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ tauPerp n = n.primeFactors.card := by
  sorry

/--
Erdős Problem 1100, variant (proved by Erdős–Hall [ErHa78]):
For all $\epsilon > 0$ and sufficiently large $x$,
$\max_{n < x} \tau^\perp(n) > \exp((\log\log x)^{2-\epsilon})$, formalized as the
existence of some $n < x$ exceeding the bound.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.erdos_hall_max :
    ∀ ε : ℝ, ε > 0 →
      ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
        ∃ n : ℕ, n < x ∧ (tauPerp n : ℝ) > exp ((log (log (x : ℝ))) ^ (2 - ε)) := by
  sorry

end Erdos1100
