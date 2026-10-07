-- [AI - Claude Sonnet 5.5]: Erdős Problem 126 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-!
# Erdős Problem #126: Prime Factors of Pairwise Sums

*Source:* [erdosproblems.com/126](https://www.erdosproblems.com/126) (status **OPEN** when
captured: "This is open, and cannot be resolved with a finite computation."; prize \$250;
captured 2026-02-20 and 2026-03-05 as the tidied problem box; **proved** since, see below).
[ErTu34] [Er95c] [Er97] [Er97e]

Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $\lvert A\rvert=n$ then
$\prod_{a\neq b\in A}(a+b)$ has at least $f(n)$ distinct prime factors. Is it true that
$f(n)/\log n\to\infty$?

Remarks recorded on the page:
* Investigated by Erdős and Turán [ErTu34] (prompted by a question of Lázár and Grünwald) in
  their first joint paper, where they proved that $\log n \ll f(n) \ll n/\log n$ (the upper bound
  is trivial, taking $A=\{1,\ldots,n\}$). Erdős says that $f(n)=o(n/\log n)$ has never been
  proved, but perhaps never seriously attacked.
* This problem has been formalised in Lean as part of the Google DeepMind Formal Conjectures
  project.

Tags: number theory. OEIS: "Possible".

**Status after capture.** The site owner's mirror (`teorth/erdosproblems`) changed this problem
from `open` to `proved` in commit `99c3925` (2026-09-03, "Problem status updates"), and to
`proved (Lean)` by `5893c69` (2026-09-05). Upstream `erdos_126` is `answer(True)` and links a
Lean proof. This second-pass review has not checked that proof. The first pass asserts the asked
("yes") direction, which is the proved direction.

**Encoding.**
* `f(n)` is a minimum over all $n$-element sets, taken in ℕ, so it exists. "$f(n)/\log n\to\infty$"
  is therefore `∀ C > 0, ∃ N, ∀ n ≥ N, ∀ A, |A| = n → (number of primes) ≥ C log n`. That is the
  first pass's statement.
* The product is over ordered pairs (`Finset.offDiag`), so each unordered pair appears twice. The
  set of prime factors is the same as for unordered pairs.
* $a\ne b$ gives $a+b\ge1$, so the product is never $0$.
* `A : Finset ℕ` allows $0\in A$. That changes small values: for $n=2$, $A=\{0,1\}$ has product
  $1$ and no prime factors, while the least value over positive integers is $1$. The change is
  asymptotically harmless. If $A_+=A\setminus\{0\}$ then the product over $A$ has at least the
  prime factors of the product over $A_+$, and $\lvert A_+\rvert\ge n-1$. So the proposition with
  $0$ allowed is equivalent to the one without.
* Brute force over $A\subseteq\{1,\dots,30\}$ gives upper bounds $1,2,2,3,4$ for $f(2),\dots,f(6)$.
  With $0$ allowed, $2$ becomes $0$ and $f(3),\dots,f(6)$ are unchanged in that search.

## References

* [ErTu34] Erdős, P. and Turán, P., _On a problem in the elementary theory of numbers_. Amer.
  Math. Monthly (1934), 608–611.
* [Er95c] Erdős, P., _Some problems in number theory_. Octogon Math. Mag. (1995), 3–5.
* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.

(Provenance: no `/latex/126` fetch exists in the session logs. [ErTu34] is from upstream
`126.lean`. [Er95c] is also in a sibling `/latex` extraction. [Er97] and [Er97e] are from the
bibliographies of upstream files for sibling problems, for example `121.lean`.)
-/

noncomputable section

/--
The number of distinct prime factors of the product ∏_{(a,b) ∈ A.offDiag} (a + b).
-/
def numPrimeFactorsPairwiseSumProd (A : Finset ℕ) : ℕ :=
  (A.offDiag.val.map (fun p : ℕ × ℕ => p.1 + p.2)).prod.primeFactors.card

/--
Erdős Problem #126 [ErTu34, Er95c, Er97, Er97e] — OPEN when captured; recorded as PROVED since
2026-09-03 (see the module docstring).

Let f(n) be maximal such that if A ⊆ ℕ has |A| = n then ∏_{a ≠ b ∈ A} (a + b)
has at least f(n) distinct prime factors. Is it true that f(n) / log n → ∞?

Erdős and Turán proved that log n ≪ f(n) ≪ n / log n (the upper bound is trivial,
taking A = {1, …, n}).

Stated as: for every constant C > 0, eventually for all n-element sets A ⊆ ℕ,
the product of pairwise sums has at least C · log n distinct prime factors.
-/
theorem erdos_problem_126 :
    ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ A : Finset ℕ, A.card = n →
          (numPrimeFactorsPairwiseSumProd A : ℝ) ≥ C * Real.log n :=
  sorry

/--
The lower bound of Erdős and Turán [ErTu34] (PROVED; a consequence of `erdos_problem_126`):
f(n) ≫ log n.
-/
theorem erdos_problem_126.variants.log_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A.card = n →
        (numPrimeFactorsPairwiseSumProd A : ℝ) ≥ c * Real.log n :=
  ⟨1, one_pos, erdos_problem_126 1 one_pos⟩

/--
The upper bound of Erdős and Turán [ErTu34] (PROVED): f(n) ≪ n / log n. The set {1, …, n} works,
since every prime factor is at most 2n.
-/
theorem erdos_problem_126.variants.upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Finset ℕ, A.card = n ∧
        (numPrimeFactorsPairwiseSumProd A : ℝ) ≤ C * ((n : ℝ) / Real.log n) :=
  sorry

/--
Erdős's remaining question (OPEN, per the page): f(n) = o(n / log n). For every ε > 0 and all large
n some n-element set has at most ε n / log n distinct prime factors in its pairwise-sum product.
-/
theorem erdos_problem_126.variants.little_o :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Finset ℕ, A.card = n ∧
        (numPrimeFactorsPairwiseSumProd A : ℝ) ≤ ε * ((n : ℝ) / Real.log n) :=
  sorry

end
