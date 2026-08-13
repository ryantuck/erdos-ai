import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open scoped ArithmeticFunction.sigma

/-!
# Erdős Problem #1061

How many solutions are there to σ(a) + σ(b) = σ(a + b) with a + b ≤ x,
where σ is the sum of divisors function? Is it ∼ cx for some constant c > 0?

A question of Erdős reported in problem B15 of Guy's collection [Gu04].

*Status:* OPEN on erdosproblems.com/1061 ("This is open, and cannot be resolved
with a finite computation"; archive captures accessed 2026-02-22 and 2026-03-06
agree). The theorem below asserts the conjectured "yes" direction of the open
question, per this repository's raw-file convention.

*Reference:*

- [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004),
  xviii+437, Problem B15. (Bibliographic data recovered from the upstream
  formal-conjectures file for this problem and from sibling files in this
  repository; not verified against erdosproblems.com/latex/1061, which was
  never fetched.)

The problem page lists OEIS A110177 as a possible related sequence (contents
not verified offline) and the tag "number theory".

Note: the authoritative upstream formalization of this problem lives in
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1061.lean`,
linked from the problem page's "Formalised statement? Yes"); it is not present
in this repository.
-/

/--
Count the number of ordered pairs (a, b) with a, b ≥ 1 and a + b ≤ n such that
σ(a) + σ(b) = σ(a + b).
-/
noncomputable def countSigmaAdditivePairs (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun p => p.1 + p.2 ≤ n ∧ σ 1 p.1 + σ 1 p.2 = σ 1 (p.1 + p.2))).card

/--
Erdős Problem #1061 [Gu04]:

How many solutions are there to σ(a) + σ(b) = σ(a + b) with a + b ≤ x,
where σ is the sum of divisors function? Is it ∼ cx for some constant c > 0?

The problem is OPEN; this raw statement asserts the conjectured "yes"
direction (a styled version would use `answer(sorry) ↔`). The count is over
ordered pairs; the symmetric equation makes the unordered count differ only
by a factor absorbed into c.
-/
theorem erdos_problem_1061 :
    ∃ c : ℝ, 0 < c ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun n => (countSigmaAdditivePairs n : ℝ))
        (fun n => c * (n : ℝ)) :=
  sorry
