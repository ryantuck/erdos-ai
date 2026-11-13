-- [AI - Claude Fable 5.2]: Erdős Problem 205 — second-pass formalization
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

open Real

/-!
# Erdős Problem #205

*Source:* [erdosproblems.com/205](https://www.erdosproblems.com/205) (status **DISPROVED (LEAN)**:
"This has been solved in the negative and the proof verified in Lean."; captured 2026-02-20; page
last edited 23 January 2026). [ErGr80, p.28]

Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k\geq 0$, where
$\Omega(m)<\log\log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with
multiplicity.) What about $<\epsilon \log\log m$? Or some more slowly growing function?

Remarks recorded on the page: it is easy to see by probabilistic methods that this holds for
almost all integers. Romanoff [Ro34] showed that a positive density set of integers are
representable as the sum of $2^k+p$ for prime $p$, and Erdős used covering systems to show that
there is a positive density set of odd integers which cannot be so represented. See also [851].
Barreto and Leeham, using ChatGPT and Aristotle, have proved a negative answer, which was
quantified by Tao and Alexeev (see the comments): in fact there are infinitely many $n$ such that,
for all $k$ with $2^k<n$, $n-2^k$ has at least
$$\gg \left(\frac{\log n}{\log\log n}\right)^{1/2}$$
many prime factors. The $n$ constructed in this way are divisible by a large power of $2$. It
remains open whether there exist arbitrarily large odd counterexamples.

## Status

DISPROVED (LEAN) at capture; the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12)
lists **disproved (Lean)** since 2026-01-10. Upstream `formal-conjectures` (`5258ab9`) states the
three parts as negations, the quantified result (with a linked Lean proof) and the open question
about odd counterexamples.

## Encoding notes

* The main theorem is the negation of the first question: for every `N` there is `n ≥ N` such
  that no `k` with `2^k ≤ n` has `Ω(n - 2^k) < log log (n - 2^k)`. It is equivalent to
  `¬ ∀ᶠ n, ∃ k m, n = 2^k + m ∧ Ω(m) < log log m` (`erdos_problem_205.iff_not_eventually`,
  PROVED in Lean).
* `Ω(m)` is `m.primeFactorsList.length`. The ℕ-subtraction `n - 2^k` is guarded by `2^k ≤ n`.
* Degenerate `m`: Lean has `Real.log 0 = 0`, so `log (log m) = 0` for `m ∈ {0, 1}`, and
  `log (log 2) < 0`; in all three cases `Ω(m) < log (log m)` is false, so these `m` never give a
  representation, as intended (`not_lt_zero`, `not_lt_one`, PROVED in Lean).
* The second and third questions (`ε log log m`, slower functions) are also answered in the
  negative by the quantified result; they are `variants.epsilon` and `variants.tao_alexeev`
  (SOLVED; not proved here). For `ε ≤ 1` the `ε`-version follows from the main statement
  (`variants.epsilon_of_le_one`, PROVED in Lean). The question about odd counterexamples is
  `variants.odd` (OPEN).

## References

From the site's `/latex/205` bibliography:
* [Ro34] Romanoff, N. P., _Über einige Sätze der additiven Zahlentheorie_. Math. Ann. (1934),
  668–678.

From other problems' site bibliographies:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.) The
  page cites p. 28.

The negative answer (Barreto and Leeham; Tao and Alexeev) is recorded on the page without a
bibliography entry ("see the comments").

*Provenance:* second pass of `conjectures/205.lean` (Fable 5.2 review,
`fable-5-2-review/205.md`).
-/

/--
Erdős Problem #205 (Disproved) [ErGr80, p.28]:

Erdős and Graham asked whether all sufficiently large n can be written as
2^k + m for some k ≥ 0, where Ω(m) < log(log(m)). Here Ω(m) is the number
of prime divisors of m counted with multiplicity, given by `(Nat.factors m).length`.

This was disproved by Barreto and Leeham. The result was quantified by Tao
and Alexeev: there are infinitely many n such that for all k with 2^k ≤ n,
n - 2^k has at least ≫ (log n / log log n)^{1/2} prime factors.

We formalize the negation of the original conjecture, which is the true statement.
-/
theorem erdos_problem_205 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) :=
  sorry

/-- The main statement is the negation of the page's first question as asked (PROVED in Lean):
"all sufficiently large `n` can be written as `2^k + m` with `Ω(m) < log log m`". -/
theorem erdos_problem_205.iff_not_eventually :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ)) ↔
    ¬ ∀ᶠ n : ℕ in Filter.atTop, ∃ k m : ℕ, n = 2 ^ k + m ∧
      (m.primeFactorsList.length : ℝ) < Real.log (Real.log (m : ℝ)) := by
  rw [Filter.eventually_atTop]
  constructor
  · rintro h ⟨N, hN⟩
    obtain ⟨n, hn, hk⟩ := h N
    obtain ⟨k, m, hnm, hlt⟩ := hN n hn
    have h1 := hk k (by omega)
    have h2 : n - 2 ^ k = m := by omega
    rw [h2] at h1
    exact absurd hlt (not_lt.2 h1)
  · intro h N
    by_contra hcon
    apply h
    refine ⟨N, fun n hn => ?_⟩
    by_contra hrep
    apply hcon
    refine ⟨n, hn, fun k hk => ?_⟩
    by_contra hlt
    exact hrep ⟨k, n - 2 ^ k, by omega, not_le.1 hlt⟩

/-- `m = 0` never gives a representation (PROVED in Lean): `Ω(0) = 0` and `log (log 0) = 0`. -/
theorem erdos_problem_205.not_lt_zero :
    ¬ (((0 : ℕ).primeFactorsList.length : ℝ) < Real.log (Real.log ((0 : ℕ) : ℝ))) := by
  simp

/-- `m = 1` never gives a representation (PROVED in Lean): `Ω(1) = 0` and `log (log 1) = 0`. -/
theorem erdos_problem_205.not_lt_one :
    ¬ (((1 : ℕ).primeFactorsList.length : ℝ) < Real.log (Real.log ((1 : ℕ) : ℝ))) := by
  simp

/-- The second question, "what about `< ε log log m`?" (SOLVED in the negative by the quantified
result on the page; not proved here): for every `ε > 0` there are arbitrarily large `n` with no
representation `n = 2^k + m`, `Ω(m) < ε log log m`. For `ε ≤ 1` this follows from the main theorem
(`variants.epsilon_of_le_one`, PROVED in Lean); for `ε > 1` it is stronger. -/
theorem erdos_problem_205.variants.epsilon :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        ε * Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) :=
  sorry

/-- For `0 < ε ≤ 1` the `ε`-version follows from the main statement (PROVED in Lean): requiring
`Ω(m) < ε log log m` with `ε ≤ 1` is more than requiring `Ω(m) < log log m`. -/
theorem erdos_problem_205.variants.epsilon_of_le_one
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        ε * Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) := by
  intro ε hε hε1 N
  obtain ⟨n, hn, hk⟩ := h N
  refine ⟨n, hn, fun k hk2 => ?_⟩
  have h1 := hk k hk2
  have h2 : (0 : ℝ) ≤ ((n - 2 ^ k).primeFactorsList.length : ℝ) := Nat.cast_nonneg _
  rcases le_total 0 (Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ))) with hL | hL
  · have h3 := mul_nonneg (sub_nonneg.2 hε1) hL
    linarith
  · have h3 := mul_nonneg hε.le (neg_nonneg.2 hL)
    linarith

/-- The quantified result of Tao and Alexeev recorded on the page (SOLVED; upstream links a Lean
proof; not proved here): for some `c > 0` there are infinitely many `n` such that, for all `k` with
`2^k < n`, `n - 2^k` has at least `c (log n / log log n)^(1/2)` prime factors. This answers the
third question ("or some more slowly growing function?") in the negative. -/
theorem erdos_problem_205.variants.tao_alexeev :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k < n →
        c * Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) :=
  sorry

/-- The page's remaining open question: are there arbitrarily large odd counterexamples? (OPEN;
the "yes" direction is asserted by the corpus convention; the page records no belief.) -/
theorem erdos_problem_205.variants.odd :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Odd n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) :=
  sorry
