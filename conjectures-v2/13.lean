import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #13

Let A ⊆ {1,...,N} be such that there are no a, b, c ∈ A with a ∣ (b + c)
and a < min(b, c). Is it true that |A| ≤ N/3 + O(1)?

Asked by Erdős and Sárközy, who observed that (2N/3, N] ∩ ℕ is such a set
(showing the N/3 bound would be optimal up to O(1)). The answer is yes,
proved by Bedert [Be23].

Status (erdosproblems.com/13, accessed 2026-03-05): PROVED — "This has been
solved in the affirmative." The problem carried a $100 prize. The
teorth/erdosproblems metadata mirror agrees: state "proved" (last update
2025-08-31), tags [number theory], OEIS A002264 (⌊n/3⌋).

For the infinite version of this problem see erdosproblems.com/12; see also
erdosproblems.com/131. In [Er92c] Erdős asks about the general version where
a ∤ (b₁ + ⋯ + b_r) whenever a < min(b₁, ..., b_r), and whether then
|A| ≤ N/(r+1) + O(1); that r-fold variant needs finite-sum machinery not
imported here and is not formalized in this file (see the upstream
formal-conjectures `erdos_13.variants.general` for a formalization).

This problem was formalized upstream in google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/13.lean`, contributed in PR #1793); the
statement below agrees with the upstream `erdos_13` up to definitional
rephrasing of the triple-free predicate.

References:

[Be23] Bedert, B., _On a problem of Erdős and Sárközy about sequences with
no term dividing the sum of two larger terms_. arXiv:2301.07065 (2023).
(Reference as given in the upstream formal-conjectures file.)

The remaining citation keys on the problem page — [Er73], [Er75b], [Er77c],
[Er92c], [Er95c], [Er97], [Er97b], [Er97e], [Er98] — are Erdős's own
problem-collection papers; full bibliographic data was not recoverable
offline and is deliberately not fabricated here.
-/

/-- A set A ⊆ {1,...,N} is *sum-divisibility-free* if there are no
    a, b, c ∈ A with a ∣ (b + c) and a < min(b, c).

    Note the elements a, b, c are not required to be distinct: a < min(b, c)
    already forces a ≠ b and a ≠ c, and taking b = c additionally forbids
    a ∣ 2b for a < b, matching the problem page's literal quantification
    (contrast problem #12, whose page says "distinct a, b, c"). This agrees
    with the upstream formal-conjectures predicate `IsForbiddenTripleFree`. -/
def IsSumDivFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < min b c → ¬(a ∣ (b + c))

/--
Erdős Problem #13 [Er73, Er75b, Er77c, Er92c, Er95c, Er97, Er97b, Er97e, Er98]:
Let A ⊆ {1,...,N} be sum-divisibility-free. Then |A| ≤ N/3 + C for some
absolute constant C.

The problem page poses this as the question "Is it true that
|A| ≤ N/3 + O(1)?"; the answer is yes, proved by Bedert [Be23], so the
statement below asserts the true (affirmative) direction.
-/
theorem erdos_problem_13 :
    ∃ C : ℝ, ∀ N : ℕ, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      IsSumDivFree A →
      (A.card : ℝ) ≤ (N : ℝ) / 3 + C :=
  sorry

/--
Erdős and Sárközy's tightness observation (recorded on the problem page):
the interval (2N/3, N] ∩ ℕ is sum-divisibility-free, and it has at least N/3
elements, so the N/3 + O(1) bound in `erdos_problem_13` is optimal up to the
O(1) term.

Here `Finset.Ioc (2 * N / 3) N` (with ℕ floor division) is exactly
(2N/3, N] ∩ ℕ: for an integer n, n > 2N/3 iff n > ⌊2N/3⌋. Its cardinality is
N - ⌊2N/3⌋ = ⌈N/3⌉ ≥ N/3. Why it is sum-divisibility-free: for a, b, c in
the interval with a < min(b, c), we have b + c ≥ 2a + 2 > 2a and
b + c ≤ 2N < 3a (as a > 2N/3), so b + c lies strictly between consecutive
multiples 2a and 3a of a, hence a ∤ (b + c).
-/
theorem erdos_problem_13.variants.tightness_witness :
    ∀ N : ℕ,
      IsSumDivFree (Finset.Ioc (2 * N / 3) N) ∧
      (N : ℝ) / 3 ≤ ((Finset.Ioc (2 * N / 3) N).card : ℝ) :=
  sorry
