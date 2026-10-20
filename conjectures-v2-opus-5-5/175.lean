-- [AI - Claude Opus 5.5]: Erdős Problem 175 — second-pass formalization
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Squarefree.Basic

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.IntervalCases
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #175

*Source:* [erdosproblems.com/175](https://www.erdosproblems.com/175) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 08 February 2026).
[Er79, p.67] [ErGr80, p.71]

Show that, for any $n\geq 5$, the binomial coefficient $\binom{2n}{n}$ is not squarefree.

Remarks recorded on the page (abridged): it is easy to see that $4\mid\binom{2n}{n}$ except when
$n=2^k$. Proved by Sárközy [Sa85] for all sufficiently large $n$, and independently by Granville and
Ramaré [GrRa96] and Velammal [Ve95] for all $n\geq 5$. If $f(n)$ is the largest integer such that,
for some prime $p$, $p^{f(n)}$ divides $\binom{2n}{n}$, then $f(n)\to\infty$ (Sander [Sa92]);
$f(n)\gg(\log n)^{1/10-o(1)}$, $f(n)\ll\log n$ for all $n$ and $f(n)\gg\log n$ for almost all
$n$ (Sander [Sa95]); $f(n)\gg(\log n)^{1/4-o(1)}$ (Erdős and Kolesnik [ErKo99]). It remains open
whether $f(n)\gg\log n$ for all $n$. Sander [Sa92b] proved that for all $0<\epsilon<1$, if $n$ is
sufficiently large and $|d|\le n^{1-\epsilon}$ then $\binom{2n+d}{n}$ is not squarefree. The
largest $n$ known for which $\binom{2n}{n}$ is not divisible by the square of an odd prime is
$n=786$ (found by Levine); Guy [Gu04] reports that Erdős 'feels sure that there are no larger such
$n$'. See also [379]; problem B33 of [Gu04].

After the capture, the mirror (`b916d95`) records `proved (Lean)` (2026-08-24), and upstream
`formal-conjectures` (`df3f12d`) links a Lean proof of the statement. Neither proof was examined
here.

## Encoding notes

* The statement is the page's, in its true direction. `n ≥ 5` is sharp: `C(8, 4) = 70` is
  squarefree, while `C(6, 3) = 20` and `C(10, 5) = 252` are not (PROVED by `decide`).
* `f n` below is the largest exponent of a prime in `C(2n, n)`; primes above `2n` do not divide it,
  so taking the maximum over `p ≤ 2n` loses nothing (`factorization_le_f`, PROVED). Sander's
  `f(n) ≪ log n` is PROVED in Lean as `f n ≤ log₂ (2n)` (`f_le_log_two`), from Mathlib's
  `Nat.factorization_choose_le_log`.

## References

From the site's `/latex/175` bibliography:
* [Sa85] Sárközy, A., _On divisors of binomial coefficients_. J. Number Theory (1985), 70–80.
* [GrRa96] Granville, A. and Ramaré, O., _Explicit bounds on exponential sums and the scarcity of
  squarefree binomial coefficients_. Mathematika (1996), 73–107.
* [Ve95] Velammal, G., _Is the binomial coefficient $\binom{2n}{n}$ squarefree?_. Hardy-Ramanujan
  J. (1995), 23–45.
* [Sa92] Sander, J. W., _Prime power divisors of binomial coefficients_. J. Reine Angew. Math.
  (1992), 1–20.
* [Sa92b] Sander, J. W., _On prime divisors of binomial coefficients_. Bull. London Math. Soc.
  (1992), 140–142.
* [Sa95] Sander, J. W., _On the order of prime powers dividing binomial coefficients_. Acta Math.
  (1995), 85–118.
* [ErKo99] Erdős, P. and Kolesnik, G., _Prime power divisors of binomial coefficients_. Discrete
  Math. (1999), 101–117.
* [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.

Erdős's sources:
* [Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. (1979), 67–70.
  (Site `/latex/144` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)

*Provenance:* second pass of `conjectures/175.lean` (Opus 5.5 review, `opus-5-5-review/175.md`).
-/

/--
Erdős Problem #175 [Er79, ErGr80]:
For any n ≥ 5, the central binomial coefficient C(2n, n) is not squarefree.
That is, there exists some prime p such that p² divides C(2n, n).
(Status: PROVED [GrRa96, Ve95]; the statement is the true direction.)
-/
theorem erdos_problem_175 :
    ∀ n : ℕ, 5 ≤ n → ¬Squarefree (Nat.choose (2 * n) n) :=
  sorry

/-- The same statement with Mathlib's `Nat.centralBinom` (PROVED in Lean, by rewriting). -/
theorem erdos_problem_175.iff_centralBinom :
    (∀ n : ℕ, 5 ≤ n → ¬Squarefree (Nat.choose (2 * n) n)) ↔
      ∀ n : ℕ, 5 ≤ n → ¬Squarefree n.centralBinom := by
  simp only [Nat.centralBinom_eq_two_mul_choose]

/-- `n ≥ 5` is sharp (PROVED by `decide` and a case check): `C(6, 3) = 20` and `C(10, 5) = 252` are
not squarefree, but `C(8, 4) = 70` is. -/
theorem erdos_problem_175.small : ¬ Squarefree (Nat.choose (2 * 3) 3) ∧ Squarefree (Nat.choose (2 * 4) 4) ∧
    ¬ Squarefree (Nat.choose (2 * 5) 5) := by
  refine ⟨by decide, ?_, by decide⟩
  rw [show Nat.choose (2 * 4) 4 = 70 by rfl, Nat.squarefree_iff_prime_squarefree]
  intro x hx hdvd
  have hle : x * x ≤ 70 := Nat.le_of_dvd (by norm_num) hdvd
  have hx8 : x ≤ 8 := by nlinarith
  interval_cases x <;> simp_all (config := {decide := true})

/-- Every prime exponent in `C(2n, n)` is at most `log_p (2n)` (PROVED in Lean; Mathlib's
`Nat.factorization_choose_le_log`, a consequence of Kummer's theorem). -/
theorem erdos_problem_175.factorization_le_log (n p : ℕ) : (Nat.choose (2 * n) n).factorization p ≤ Nat.log p (2 * n) :=
  Nat.factorization_choose_le_log

/-- `f n`: the largest `e` such that `p ^ e ∣ C(2n, n)` for some prime `p` (review addition). -/
noncomputable def erdos_problem_175.f (n : ℕ) : ℕ :=
  (Finset.range (2 * n + 1)).sup (fun p => (Nat.choose (2 * n) n).factorization p)

/-- `f n` bounds the exponent of every prime, including primes above `2n` (PROVED in Lean). -/
theorem erdos_problem_175.factorization_le_f (n p : ℕ) : (Nat.choose (2 * n) n).factorization p ≤ erdos_problem_175.f n := by
  rcases Nat.lt_or_ge (2 * n) p with hp | hp
  · rw [← Nat.centralBinom_eq_two_mul_choose, Nat.factorization_centralBinom_eq_zero_of_two_mul_lt hp]
    exact Nat.zero_le _
  · exact Finset.le_sup (f := fun p => (Nat.choose (2 * n) n).factorization p)
      (Finset.mem_range.mpr (by omega))

/-- Sander's upper bound [Sa95], `f(n) ≪ log n` (PROVED in Lean): `f n ≤ log₂ (2n)`. -/
theorem erdos_problem_175.f_le_log_two (n : ℕ) : erdos_problem_175.f n ≤ Nat.log 2 (2 * n) := by
  unfold erdos_problem_175.f
  apply Finset.sup_le
  intro p _
  refine le_trans (erdos_problem_175.factorization_le_log n p) ?_
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp
  · exact Nat.log_anti_left (by norm_num) hp

/-- Sander [Sa92] (SOLVED; not proved here): `f(n) → ∞`. -/
theorem erdos_problem_175.variants.sander_tendsto :
    Filter.Tendsto erdos_problem_175.f Filter.atTop Filter.atTop :=
  sorry

/-- Erdős and Kolesnik [ErKo99] (SOLVED; not proved here): $f(n)\gg(\log n)^{1/4-o(1)}$. -/
theorem erdos_problem_175.variants.erdos_kolesnik :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (erdos_problem_175.f n : ℝ) :=
  sorry

/-- The open question on the page (OPEN): is $f(n)\gg\log n$ for all (large) `n`? Stated in the
"yes" direction. -/
theorem erdos_problem_175.variants.log_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ≤ (erdos_problem_175.f n : ℝ) :=
  sorry

/-- Sander [Sa92b] (SOLVED; not proved here): for `0 < ε < 1`, large `n` and `|d| ≤ n^(1-ε)`,
`C(2n + d, n)` is not squarefree. -/
theorem erdos_problem_175.variants.sander_shift :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ d : ℤ,
      (|d| : ℝ) ≤ (n : ℝ) ^ (1 - ε) → ¬Squarefree (Nat.choose (2 * (n : ℤ) + d).toNat n) :=
  sorry

/-- Erdős's belief, reported by Guy [Gu04] (OPEN): for `n > 786`, `C(2n, n)` is divisible by the
square of an odd prime. (The review's computation confirms this for `786 < n ≤ 10⁷`.) -/
theorem erdos_problem_175.variants.odd_square :
    ∀ n : ℕ, 786 < n → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ Nat.choose (2 * n) n :=
  sorry
