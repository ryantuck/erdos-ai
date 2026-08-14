import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset

noncomputable section

/-!
# Erdős Problem #1108

Let A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }. If k ≥ 2, does A contain only
finitely many k-th powers? Does it contain only finitely many powerful numbers?

**Status: OPEN** (erdosproblems.com banner; page edition 04 November 2025,
accessed 2026-03-09).

Asked by Erdős at Oberwolfach in 1988 [Ob1]. It is open even whether there are
infinitely many squares of the form 1 + n! (see problem #398).

This was motivated in part by a problem of Mahler, which he discussed with
Erdős a few days before his death in 1988: if k ≥ 5 and
A_k = { ∑_{n ∈ S} k^n : S ⊂ ℕ finite }, does A_k contain only finitely many
squares? Mahler showed that there are infinitely many squares in A_k for
k ≤ 4, and found only one square for k ≥ 5, namely 1 + 7 + 7² + 7³ = 400.
Brindza and Erdős [BrEr91] proved that, for any r, if n₁! + ⋯ + n_r! is
powerful then n₁ ≪_r 1.

Note on the ℕ convention: Mahler's example 400 = 7⁰ + 7¹ + 7² + 7³ (on the
same problem page) uses the exponent 0, so the source's "S ⊂ ℕ finite"
includes 0. Hence `S : Finset ℕ` below is the intended reading; in
particular both 0! = 1 and 1! = 1 are available as summands, so e.g.
4 = 0! + 1! + 2! lies in A (it would not if indices started at 1). This
matches the official formalization linked from the page
(google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1108.lean).

## References

Bibliographic details below are honest stubs recovered from the archived
problem page and sibling files in this repo (the [BrEr91] entry is carried
by problem #405's file); no /latex/1108 capture exists, so full verification
awaits network access to erdosproblems.com/latex/1108.

- [Ob1] Oberwolfach problem session. (Sibling files render this key as
  "Oberwolfach problem session (1986)", while this problem was asked at
  Oberwolfach in 1988; the authoritative expansion is DEFERRED.)
- [BrEr91] Brindza, B. and Erdős, P., _On some Diophantine problems
  involving powers and factorials_. J. Austral. Math. Soc. Ser. A 51
  (1991), 1-7.

https://www.erdosproblems.com/1108
Tags: number theory, factorials
Related OEIS sequences: A051761, A115645, A025494
-/

/-- The set A of all sums of distinct factorials: A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }.
    Note that 0 ∈ S is allowed (matching the source's ℕ), so 0! = 1 and 1! = 1 may
    both occur as summands; the empty S gives 0 ∈ A. -/
def IsFactorialSubsetSum1108 (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial

/-- A positive natural number n is **powerful** if for every prime p dividing n,
    we have p² ∣ n. (In particular 1 is powerful, vacuously; the positivity
    conjunct excludes 0, matching the standard convention.) -/
def IsPowerful1108 (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The set A_k of all sums of distinct powers of k:
    A_k = { ∑_{n ∈ S} k^n : S ⊂ ℕ finite }, from Mahler's motivating problem.
    Note 0 ∈ S is allowed (k⁰ = 1): Mahler's square 400 = 7⁰ + 7¹ + 7² + 7³
    uses it. -/
def IsPowerSubsetSum1108 (k m : ℕ) : Prop :=
  ∃ S : Finset ℕ, m = ∑ n ∈ S, k ^ n

/--
Erdős Problem #1108, part 1 [Ob1]:

If k ≥ 2, does A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contain only finitely
many k-th powers?

This question is OPEN; the statement below asserts the conjectured
affirmative direction ("only finitely many"), following this corpus's
convention for open yes/no questions. It is open even for squares of the
special form 1 + n! (problem #398).
-/
theorem erdos_problem_1108a (k : ℕ) (hk : 2 ≤ k) :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ ∃ b : ℕ, m = b ^ k} :=
  sorry

/--
Erdős Problem #1108, part 2 [Ob1]:

Does A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contain only finitely many powerful
numbers?

This question is OPEN; the statement below asserts the conjectured
affirmative direction, following this corpus's convention for open yes/no
questions. For sums of a *bounded* number of factorials the answer is yes,
by Brindza–Erdős [BrEr91] (see `erdos_problem_1108_brindza_erdos` below).
-/
theorem erdos_problem_1108b :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ IsPowerful1108 m} :=
  sorry

/--
Variant (Brindza–Erdős [BrEr91], solved): for any r, if n₁! + ⋯ + n_r! is
powerful then n₁ ≪_r 1.

Encoded as: for each r there is a bound C = C(r) such that whenever a sum of
r factorials (repetitions allowed, in any order) is powerful, every argument
n_i is at most C — equivalently, the largest argument n₁ is bounded in terms
of r alone. For r = 0 the empty sum is 0, which is not powerful (positivity),
so the hypothesis is vacuous there.
-/
theorem erdos_problem_1108_brindza_erdos (r : ℕ) :
    ∃ C : ℕ, ∀ f : ℕ → ℕ,
      IsPowerful1108 (∑ i ∈ range r, (f i).factorial) →
      ∀ i < r, f i ≤ C :=
  sorry

/--
Variant (Mahler's question, OPEN — the motivating problem recorded on the
page): if k ≥ 5, does A_k = { ∑_{n ∈ S} k^n : S ⊂ ℕ finite } contain only
finitely many squares?

Mahler found only one square in A_k for k ≥ 5, namely
1 + 7 + 7² + 7³ = 400 = 20². The statement below asserts the conjectured
affirmative direction, following this corpus's convention for open yes/no
questions.
-/
theorem erdos_problem_1108_mahler_question (k : ℕ) (hk : 5 ≤ k) :
    Set.Finite {m : ℕ | IsPowerSubsetSum1108 k m ∧ ∃ b : ℕ, m = b ^ 2} :=
  sorry

/--
Variant (Mahler, solved): for 2 ≤ k ≤ 4 there are infinitely many squares
in A_k = { ∑_{n ∈ S} k^n : S ⊂ ℕ finite }.

The page states this for "k ≤ 4"; the hypothesis 2 ≤ k restricts to the
substantive bases. (For k = 1 the claim is trivially true since A_1 = ℕ;
for k = 0, under Lean's 0⁰ = 1 convention A_0 = {0, 1}, so the k = 0 case
would be false and is plainly outside Mahler's intent.)
-/
theorem erdos_problem_1108_mahler_small (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    ¬ Set.Finite {m : ℕ | IsPowerSubsetSum1108 k m ∧ ∃ b : ℕ, m = b ^ 2} :=
  sorry

end
