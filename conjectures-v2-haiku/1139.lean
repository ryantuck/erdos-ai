import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #1139

Let $1 \leq u_1 < u_2 < \cdots$ be the sequence of integers with at most $2$
prime factors (counted with multiplicity). Is it true that
$$\limsup \frac{u_{k+1} - u_k}{\log k} = \infty?$$

**Status:** OPEN. The page edition was 2026-01-23, accessed 2026-03-09.

**Tags:** number theory, primes

The problem asks whether the gaps between consecutive 2-almost-primes grow faster than
log k on average. The formalization below uses 0-indexed enumeration via `Nat.nth`.

**Reference:**

- [Va99] Various. _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999). Section 1.4.

**Related upstream formalization:**
  https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1139.lean
  (styled version using `answer(sorry) ↔ atTop.limsup (… : EReal) = ⊤`)
-/

/-- A positive integer has at most 2 prime factors (counted with multiplicity).
    Equivalent to $\Omega(n) \le 2$, where $\Omega$ counts prime factors with
    multiplicity. This is the standard definition of 2-almost-primes. -/
def hasAtMostTwoPrimeFactors (n : ℕ) : Prop :=
  1 ≤ n ∧ n.primeFactorsList.length ≤ 2

/-- The k-th element (0-indexed) of the increasing sequence of positive integers
    with at most 2 prime factors. The sequence starts: 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, ....
    The predicate is infinite (contains all primes), so nth never returns 0 due to exhaustion.
    Thus almostPrime2 is strictly increasing. -/
noncomputable def almostPrime2 (k : ℕ) : ℕ :=
  nth hasAtMostTwoPrimeFactors k

/-- Gap between consecutive elements of the sequence.
    Since almostPrime2 is strictly monotone (via Nat.nth_lt_nth applied to an infinite predicate),
    almostPrime2 (k + 1) > almostPrime2 k always, so ℕ subtraction never truncates. -/
noncomputable def almostPrime2Gap (k : ℕ) : ℕ :=
  almostPrime2 (k + 1) - almostPrime2 k

/--
Erdős Problem #1139 [Va99, 1.4]:

Let 1 ≤ u₁ < u₂ < ⋯ be the sequence of positive integers with at most 2 prime
factors (counted with multiplicity). Is it true that
  limsup (u_{k+1} - u_k) / log k = ∞?

The raw corpus convention for open yes/no questions is to state the conjectured direction
as a bare assertion (since the `answer()` elaborator is unavailable in this pipeline).
The statement below asserts the conjectured "yes" direction: for every M > 0, there exist
arbitrarily large k such that the gap u_{k+1} - u_k exceeds M · log k.

**Indexing note:** almostPrime2 is 0-indexed, so almostPrime2(k) corresponds to u_{k+1}
in the source's 1-indexed notation. The gap almostPrime2Gap(k) = almostPrime2(k+1) - almostPrime2(k)
corresponds to u_{k+2} - u_{k+1} in source notation. The inequality uses log(k+1) as the denominator
to make the indexing term-by-term exact: the source asks about the ratio at index j in the source
sequence, which maps to log(j) in the source; this is log(k+1) in 0-indexed Lean notation.

**Mathematical equivalence:** limsup (gap k / log(k+1)) = ∞ is captured by:
  ∀ M > 0, ∀ N, ∃ k ≥ N, M · log(k+1) < gap k.

The slightly weaker form (with log k) is provably equivalent: bounds with M log k and 2M log(k+1)
relate via monotonicity of log on [1,∞) and the fact that log(k+1) ≤ 2 log k for k ≥ 2.
-/
theorem erdos_problem_1139 :
    ∀ M : ℝ, M > 0 → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      M * Real.log ((k : ℝ) + 1) < (almostPrime2Gap k : ℝ) :=
  sorry

end
