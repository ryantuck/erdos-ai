import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

noncomputable section

/--
The Erdős prime gap expression at index n:
  (log log n · log log log log n) / (log log log n)² · log n

This is the function appearing in Erdős' conjecture on large gaps between
consecutive primes.

Degenerate-input behavior (Lean `Real.log` junk values; all harmless for the
infinitely-many statements below, which are determined by arbitrarily large n):
- n ≤ 2: iterated logs hit non-positive arguments (`Real.log x = 0` for
  x ≤ 0), and at n = 2 the denominator is 0, so real division-by-zero
  returns 0; the value is 0.
- 3 ≤ n ≤ 15 (n < e^e): log log log n < 0, so the fourth iterated log is
  `Real.log` of a negative number, i.e. 0; the value is 0.
- 16 ≤ n ≤ 3 814 279 (n < e^(e^e)): log log log n ∈ (0,1), so
  log log log log n is genuinely negative and the value is negative.
- n ≥ 3 814 280 (n > e^(e^e)): every factor is positive and the value is
  the intended expression.
-/
def erdosPrimeGapBound (n : ℕ) : ℝ :=
  let x := (n : ℝ)
  (Real.log (Real.log x) * Real.log (Real.log (Real.log (Real.log x)))) /
    (Real.log (Real.log (Real.log x))) ^ 2 * Real.log x

/--
The improved Ford–Green–Konyagin–Maynard–Tao prime gap expression [FGKMT18]:
  (log log n · log log log log n) / (log log log n) · log n
— the Erdős expression with the square removed from the denominator. The same
degenerate small-n behavior as `erdosPrimeGapBound` applies (value ≤ 0 for
n ≤ e^(e^e) ≈ 3.81 × 10⁶; no division by zero occurs for n ≥ 3, and at
n ≤ 2 the junk value is 0), and is harmless for the same reason.
-/
def fgkmtPrimeGapBound (n : ℕ) : ℝ :=
  let x := (n : ℝ)
  (Real.log (Real.log x) * Real.log (Real.log (Real.log (Real.log x)))) /
    Real.log (Real.log (Real.log x)) * Real.log x

/--
Erdős Problem #4 [Er55c, Er57, Er61, Er65b, Er81k, Er82e, Er90, Er97c, Er97f,
Va99]:

Is it true that, for any C > 0, there are infinitely many n such that
  p_{n+1} - pₙ > C · (log log n · log log log log n) / (log log log n)² · log n?

SOLVED in the affirmative (erdosproblems.com status: PROVED, $10000 prize;
page last edited 23 January 2026, accessed 2026-02-18; status cross-checked
"proved" against the teorth/erdosproblems metadata mirror, last update
2025-08-31). The statement below asserts the affirmed direction directly.

The peculiar quantitative form was motivated by an old result of Rankin
[Ra38] (1938), who proved the claim for some fixed C > 0 (see variant below).
Solved by Maynard [Ma16] (2016) and Ford–Green–Konyagin–Tao [FGKT16] (2016).
The best bound, due to all five authors [FGKMT18] (2018), removes the square
in the denominator: infinitely many n satisfy
  p_{n+1} - pₙ ≫ (log log n · log log log log n) / (log log log n) · log n
(see variant below). The likely truth is a lower bound like ≫ (log n)² (see
variant below). In [Er97c] Erdős revised the value of this problem to $5000
and reserved the $10000 for a lower bound > (log n)^{1+c} for some c > 0.
The best known upper bound is p_{n+1} - pₙ ≪ n^{0.525+o(1)}, proved by
Baker, Harman, and Pintz [BHP01].

Here `nth Nat.Prime` is 0-indexed (p₀ = 2, p₁ = 3, …), so the index n is
shifted by one against the source's 1-indexed pₙ; since the bound function
changes by a factor 1 + o(1) under a unit index shift and the claim is
quantified over all C > 0, the two readings are equivalent. Only finitely
many n take the degenerate small-n values of `erdosPrimeGapBound` (see its
docstring), so the infinitely-many statement is unaffected.

Related OEIS sequence: A002386 (record prime gaps). See also Erdős problem
[687] (Jacobsthal-type covering by prime residue classes, the mechanism
behind [FGKMT18]). This is discussed in problem A8 of Guy's collection
[Gu04]. Tags: number theory, primes.

References (recovered from the archived page and sibling files in this repo;
entries marked "stub" lack full journal/volume/page data, which is DEFERRED,
not fabricated — see erdosproblems.com/latex/4):
- [Er55c] Erdős, P., Some problems on number theory (1955). (stub; page
  cites p.2)
- [Er57] Erdős, P., Some unsolved problems (1957). (stub; page cites p.292)
- [Er61] Erdős, P., Some unsolved problems. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254. (page cites p.223)
- [Er65b] Erdős, P., Some recent advances and current problems in number
  theory. Lectures on Modern Mathematics III (1965), 196-244. (page cites
  p.201, consistent with this range; sibling files disagree on the title of
  this key)
- [Er81k] Erdős, P. (1981). (stub; page cites p.1)
- [Er82e] Erdős, P. (1982). (stub; sibling files disagree on the title, and
  the page's citation p.64 is inconsistent with the page range of the most
  common sibling entry)
- [Er90] Erdős, P., Some of my favourite unsolved problems. A tribute to
  Paul Erdős (1990), 467-478.
- [Er97c] Erdős, P., Some of my favorite problems and results. The
  mathematics of Paul Erdős, I (1997). (sibling files disagree on the title
  of this key)
- [Er97f] Erdős, P. (1997). (stub; sibling files disagree on the title)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest (1999). (page cites
  problem 1.1)
- [Ra38] Rankin, R. A., The Difference between Consecutive Prime Numbers.
  Journal of the London Mathematical Society (1938), 242-247.
- [Ma16] Maynard, J. (2016). (stub; from page prose)
- [FGKT16] Ford, K., Green, B., Konyagin, S., and Tao, T. (2016). (stub;
  from page prose)
- [FGKMT18] Ford, K., Green, B., Konyagin, S., Maynard, J., Tao, T., Long
  gaps between primes. Journal of the American Mathematical Society (2018),
  65-105.
- [BHP01] Baker, R., Harman, G., and Pintz, J. (2001). (stub; from page
  prose)
- [Gu04] Guy, R. K., Unsolved problems in number theory (2004), xviii+437.
-/
theorem erdos_problem_4 :
    ∀ C : ℝ, 0 < C →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        (nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ) >
          C * erdosPrimeGapBound n :=
  sorry

/--
Erdős Problem #4, Rankin's theorem [Ra38]:

There exists some constant C > 0 such that there are infinitely many n with
  p_{n+1} - pₙ > C · (log log n · log log log log n) / (log log log n)² · log n.
This 1938 result motivated the quantitative form of Erdős' question; the
full problem (proved by [Ma16] and [FGKT16]) upgrades "some C" to "every C".
-/
theorem erdos_problem_4.variants.rankin :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        (nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ) >
          C * erdosPrimeGapBound n :=
  sorry

/--
Erdős Problem #4, best known bound [FGKMT18]:

Ford, Green, Konyagin, Maynard, and Tao (2018) proved that there are
infinitely many n such that
  p_{n+1} - pₙ ≫ (log log n · log log log log n) / (log log log n) · log n,
removing the square from the denominator of the Erdős expression. Stated in
the ≫ (i.e. ∃ C > 0) form given on the problem page. For n large the
denominator log log log n exceeds 1, so this expression eventually dominates
`erdosPrimeGapBound`.
-/
theorem erdos_problem_4.variants.ford_green_konyagin_maynard_tao :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        (nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ) >
          C * fgkmtPrimeGapBound n :=
  sorry

/--
Erdős Problem #4, conjectured true order of growth (OPEN):

Per the problem page, "the likely truth is a lower bound like ≫ (log n)²",
i.e. there exists C > 0 such that infinitely many n satisfy
  p_{n+1} - pₙ > C (log n)².
Stated in the ≫ (i.e. ∃ C > 0) form: under Cramér-type conjectures the
limsup of (p_{n+1} - pₙ)/(log pₙ)² is a finite constant, so the ∀ C form
would be false. In [Er97c] Erdős reserved the $10000 for the intermediate
lower bound > (log n)^{1+c} for some c > 0 (not formalized here: real
exponents need `rpow`, which this file does not import).
-/
theorem erdos_problem_4.variants.log_squared :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
        (nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ) >
          C * (Real.log (n : ℝ)) ^ 2 :=
  sorry

end
