import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ArithmeticFunction.sigma

/-!
# Erdős Problem #1060

Source: https://www.erdosproblems.com/1060 (page last edited 28 September 2025;
archived captures accessed 2026-02-22 and 2026-03-06).

Verbatim statement: "Let $f(n)$ count the number of solutions to $k\sigma(k)=n$,
where $\sigma(k)$ is the sum of divisors of $k$. Is it true that
$f(n)\leq n^{o(\frac{1}{\log\log n})}$? Perhaps even $\leq (\log n)^{O(1)}$?"

Status: OPEN ("This is open, and cannot be resolved with a finite computation").
This is discussed in problem B11 of Guy's collection [Gu04]. Tags: number theory.
Related OEIS sequence: A327153. An upstream formalisation exists at
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/1060.lean`.

Both questions are stated below as direct assertions of the conjectured ("yes")
direction, per raw-file convention; a styled version should use the
`answer(sorry) ↔` question form, since the problem is open.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), xviii+437.
(Bibliographic stub recovered from sibling files sharing this key; not verified
against erdosproblems.com/latex/1060, which was not captured in the session logs.)
-/

/--
The number of solutions k to k * σ(k) = n.

Restricting k to `Finset.Icc 1 n` loses no solutions: for k ≥ 1 we have
σ(k) ≥ 1, so k · σ(k) = n forces k ≤ n (in fact k ≤ √n, since σ(k) ≥ k).
The excluded k = 0 satisfies k · σ(k) = 0 only for n = 0, where the intended
count over positive integers is 0, matching `countSolns 0 = 0`.
-/
noncomputable def countSolns (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).filter (fun k => k * σ 1 k = n) |>.card

/--
Erdős Problem #1060 [Gu04]:

Let f(n) count the number of solutions to k·σ(k) = n, where σ(k) is the sum
of divisors of k. Is it true that f(n) ≤ n^{o(1/log log n)}?

More precisely, for every ε > 0, there exists N such that for all n ≥ N,
f(n) ≤ n^{ε / log(log n)}.

Perhaps even f(n) ≤ (log n)^{O(1)}?

(For n ≤ 2 the right-hand side involves Lean junk values — `Real.log x = 0` for
x ≤ 0 and division by zero equals 0 — but these indices are absorbed by the
"sufficiently large" quantifier and do not affect the statement's meaning;
log log n > 0 for all n ≥ 3.)
-/
theorem erdos_problem_1060_weak :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (countSolns n : ℝ) ≤ (n : ℝ) ^ (ε / Real.log (Real.log n)) :=
  sorry

/--
Stronger form of Erdős Problem #1060: f(n) ≤ (log n)^{O(1)}.

There exists a constant C such that for all n ≥ 2,
the number of solutions to k·σ(k) = n is at most (log n)^C.

(The global "∀ n ≥ 2" form is equivalent to the eventual f(n) ≤ (log n)^{O(1)}
convention: the smallest n ≥ 2 with a solution is n = 6 = 2·σ(2), and
log 6 > 1, so any finitely many initial cases with f(n) ≥ 1 are covered by
enlarging C; for n ∈ {2, 3, 4, 5}, f(n) = 0 and the bound holds trivially.)
-/
theorem erdos_problem_1060_strong :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        (countSolns n : ℝ) ≤ (Real.log n) ^ C :=
  sorry
