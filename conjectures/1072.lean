import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1072

For any prime p, let f(p) be the least integer such that f(p)! + 1 ≡ 0
(mod p) — equivalently, the least m with p ∣ m! + 1, i.e. m! ≡ -1 (mod p).
This file takes m to range over *positive* integers; the two readings
differ only at p = 2 (0! + 1 = 2, so a reading allowing m = 0 would give
f(2) = 0 instead of f(2) = 1 = 2 - 1), which affects neither question
below.

By Wilson's theorem, (p-1)! ≡ -1 (mod p) for every prime p, so f(p) is
well-defined and f(p) ≤ p - 1.

**Part (a):** Is it true that there are infinitely many primes p for which
f(p) = p - 1?

**Part (b):** Is it true that f(p)/p → 0 for almost all primes p?

Both questions are OPEN (page edition 04 October 2025). They were
formulated by Erdős, Hardy, and Subbarao [HaSu02], who believed that the
number of p ≤ x for which f(p) = p - 1 is o(x/log x) (formalized below as
`erdos_problem_1072_littleo`). These are mentioned in problem A2 of Guy's
collection [Gu04].

Related OEIS sequences: A073944, A072937, A154554.

References:

[HaSu02] Hardy, G. E. and Subbarao, M. V., *A modified problem of Pillai
and some related questions*. Amer. Math. Monthly (2002), 554–559. (Volume
number not recoverable offline — deliberately omitted, not lost.)

[Gu04] Guy, R. K., *Unsolved problems in number theory*. 3rd ed., Springer
(2004). Problem A2.

https://www.erdosproblems.com/1072
(Archived captures accessed 2026-02-22 and 2026-03-09, in agreement. The
problem is also formalized upstream in google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/1072.lean, which is the authoritative
artifact for that repository and is not present in this repo.)
-/

/-- For a prime p, there exists m such that p ∣ m! + 1.
    By Wilson's theorem, m = p - 1 always works. -/
private lemma exists_factorial_mod (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, 0 < m ∧ p ∣ (m.factorial + 1) :=
  ⟨p - 1, Nat.sub_pos_of_lt (hp.one_lt), by sorry⟩

/-- f(p): the least positive integer m such that p ∣ m! + 1. -/
noncomputable def erdos1072_f (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  Nat.find (exists_factorial_mod p hp)

/--
Erdős Problem #1072, Part (a) [HaSu02] (OPEN):

Is it true that there are infinitely many primes p for which f(p) = p - 1,
i.e., p - 1 is the least m with p ∣ m! + 1? This theorem states the
question's "yes" direction, as is this repo's raw-file convention for open
yes/no questions.
-/
theorem erdos_problem_1072a :
    Set.Infinite {p : ℕ | ∃ hp : Nat.Prime p, erdos1072_f p hp = p - 1} :=
  sorry

/-- Count of primes p ≤ N satisfying predicate P. -/
noncomputable def countPrimesSat1072 (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => Nat.Prime p ∧ P p)).card

/-- Count of primes p ≤ N. -/
noncomputable def countPrimes1072 (N : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => Nat.Prime p)).card

/--
Erdős Problem #1072, Part (b) [HaSu02] (OPEN):

Is it true that f(p)/p → 0 for almost all primes p? This theorem states
the question's "yes" direction. Formulated as: for every ε > 0,
the proportion of primes p ≤ N with f(p) ≥ ε · p tends to 0 as N → ∞.
(This "convergence in relative density" form is equivalent to the
existence of a relative-density-1 set of primes along which f(p)/p → 0,
which is how the upstream formal-conjectures file states it.)
-/
theorem erdos_problem_1072b :
    ∀ ε : ℝ, ε > 0 →
    Tendsto
      (fun N : ℕ =>
        (countPrimesSat1072
          (fun p => ∃ hp : Nat.Prime p, (erdos1072_f p hp : ℝ) ≥ ε * (p : ℝ)) N : ℝ) /
          (countPrimes1072 N : ℝ))
      atTop (nhds 0) :=
  sorry

/--
Erdős Problem #1072, belief of Erdős, Hardy, and Subbarao [HaSu02]:

The number of primes p ≤ x with f(p) = p - 1 is o(x / log x).

Stated here in the equivalent form (by Chebyshev's bounds
π(x) ≍ x / log x): the primes p with f(p) = p - 1 have relative density 0
among all primes. This form uses only the counting functions this file
already defines (avoiding a new import for Real.log); the literal page
statement is the o(x / log x) one. The upstream
google-deepmind/formal-conjectures file records the same belief as
`erdos_1072a.variants.littleo`.
-/
theorem erdos_problem_1072_littleo :
    Tendsto
      (fun N : ℕ =>
        (countPrimesSat1072
          (fun p => ∃ hp : Nat.Prime p, erdos1072_f p hp = p - 1) N : ℝ) /
          (countPrimes1072 N : ℝ))
      atTop (nhds 0) :=
  sorry

end
