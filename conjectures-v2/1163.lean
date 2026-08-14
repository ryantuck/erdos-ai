import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1163

Describe (by statistical means) the arithmetic structure of the orders of
subgroups of Sₙ.

A problem of Erdős and Turán [Va99, 5.74]. Status on erdosproblems.com: OPEN
("This is open, and cannot be resolved with a finite computation"). The site
owner writes: "I have reproduced the problem verbatim; I am not entirely sure
what it is asking for", and the page adds "The original source is ambiguous as
to what the problem is". The teorth/erdosproblems metadata mirror confirms
status `open`, last update 2026-01-23, unformalized.

The theorem below formalizes ONE concrete interpretation, chosen by the
formalizer — it does not appear on the problem page: the proportion of
divisors of n! that occur as orders of subgroups of Sₙ tends to 0 as n → ∞.
By Lagrange's theorem every subgroup order divides |Sₙ| = n!, so the subgroup
orders form a subset of the divisors of n!; the interpretation conjectures
that this subset is asymptotically negligible. To the reviewer's knowledge the
truth of this interpretation is itself open. It is a genuinely asymptotic
claim: for n ≤ 4 every divisor of n! is a subgroup order of Sₙ, and for S₅
exactly 13 of the 16 divisors of 120 are (15, 30 and 40 are not).

See Erdős Problem #1162 for the companion Erdős–Turán question [Va99, 5.73]
on the number of subgroups of Sₙ; its vague second part ("is there a
statistical theorem on their order?") is close in spirit to this problem.

Reference (stub recovered from archived pipeline logs; not independently
verified against the live bibliography):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999.

Tags: group theory
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Equiv

/-- A natural number m is a subgroup order of Sₙ if there exists a subgroup
    of the symmetric group Perm(Fin n) with exactly m elements. -/
def IsSubgroupOrderOfSn (n m : ℕ) : Prop :=
  ∃ H : Subgroup (Perm (Fin n)), Nat.card H = m

/--
Erdős Problem #1163 (Erdős and Turán) [Va99, 5.74]:
Describe (by statistical means) the arithmetic structure of the orders of
subgroups of Sₙ.

The original problem is acknowledged as ambiguous (the problem-page owner is
"not entirely sure what it is asking for"). The statement below is a concrete
interpretation chosen by the formalizer: as n → ∞, the proportion of divisors
of n! that are orders of subgroups of Sₙ tends to 0. By Lagrange's theorem
every subgroup order divides n!, so the divisors of n! contain all subgroup
orders; the interpretation conjectures that they form a vanishing fraction of
all divisors. This interpretation is not stated on the problem page, and its
truth value is, to the reviewer's knowledge, itself open.
-/
theorem erdos_problem_1163 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ((n.factorial.divisors.filter (fun m => IsSubgroupOrderOfSn n m)).card : ℝ) <
        ε * (n.factorial.divisors.card : ℝ) := by
  sorry

end
