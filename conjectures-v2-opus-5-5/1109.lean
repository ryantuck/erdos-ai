-- [AI-Generated]: Erdős Problem 1109 — second-pass formalization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Pointwise Real

/-!
# Erdős Problem #1109

*Source:* [erdosproblems.com/1109](https://www.erdosproblems.com/1109) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
03 December 2025, captured 2026-02-23). [ErSa87]

Let f(N) be the size of the largest subset A ⊆ {1, …, N} such that every n ∈ A + A is
squarefree. Estimate f(N). In particular, is it true that f(N) ≤ N^{o(1)}, or even
f(N) ≤ (log N)^{O(1)}?

Both sub-questions are formalized, in their asked ("yes") direction as direct assertions:
the stronger one as `erdos_problem_1109_conjecture` and the weaker one as
`erdos_problem_1109_subpolynomial`.

First studied by Erdős and Sárközy [ErSa87], who proved log N ≪ f(N) ≪ N^{3/4} log N
and guessed the lower bound is nearer the truth. Sárközy [Sa92c] extended this to the case
of A + B, and to sumsets which are k-power-free. Gyarmati [Gy01] gave an alternative proof
of f(N) ≫ log N and new bounds for the case of A + B. Konyagin [Ko04] improved this to
(log log N)(log N)² ≪ f(N) ≪ N^{11/15 + o(1)}. The infinite analogue of this problem is
#1103; upper bounds for f(N) directly imply lower bounds for the aⱼ considered there.

Computation (review scratch script, exact maximum-clique search): f(N) for N = 1, …, 150
first attains the values 1, 2, …, 12 at N = 1, 5, 19, 23, 37, 41, 59, 87, 101, 105, 113,
131.

Tags: number theory. OEIS: A392164, A392165. The page records "Formalised statement? No"
as of capture.

## References

* [ErSa87] Erdős, P. and Sárközy, A., _On divisibility properties of integers of the form
  a + a'_. Acta Math. Hungar. (1987), 117–122.
* [Sa92c] Sárközy, G. N., _On a problem of P. Erdős_. Acta Math. Hungar. (1992), 271–282.
* [Gy01] Gyarmati, K., _On divisibility properties of integers of the form ab + 1_. Period.
  Math. Hungar. (2001), 71–79.
* [Ko04] Konyagin, S. V., _Problems of the set of square-free numbers_. Izv. Ross. Akad.
  Nauk Ser. Mat. (2004), 63–90.

(As extracted by the original pipeline's fetch of `erdosproblems.com/latex/1109`; volume
numbers are not in that extraction.)
-/

/--
Erdős Problem #1109 (the stronger question; OPEN) [ErSa87]:
Let f(N) be the size of the largest subset A ⊆ {1, ..., N} such that every
n ∈ A + A is squarefree. Is it true that f(N) ≤ (log N)^{O(1)}?

Formalized as: there exist constants C > 0 and k > 0 such that for all
sufficiently large N, every subset A ⊆ {1, ..., N} whose sumset A + A is
entirely squarefree satisfies |A| ≤ C · (log N)^k.

First studied by Erdős and Sárközy [ErSa87], who proved
  log N ≪ f(N) ≪ N^{3/4} · log N.
Konyagin [Ko04] improved this to
  (log log N) · (log N)² ≪ f(N) ≪ N^{11/15 + o(1)}.
-/
theorem erdos_problem_1109_conjecture :
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℕ, 0 < k ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ C * (Real.log N) ^ k :=
  sorry

/--
Erdős Problem #1109 (the weaker question; OPEN) [ErSa87]: is f(N) ≤ N^{o(1)}?

That is, for every ε > 0 and all sufficiently large N, every A ⊆ {1, …, N} with A + A
squarefree has |A| ≤ N^ε. It is written as `log |A| ≤ ε · log N`, which is equivalent
(including |A| = 0, since `Real.log 0 = 0`), because this file has no real powers. It is
implied by `erdos_problem_1109_conjecture`. The first-pass file omitted this sub-question
from both the statement and the quoted problem text.
-/
theorem erdos_problem_1109_subpolynomial :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      Real.log (A.card : ℝ) ≤ ε * Real.log N :=
  sorry

/--
Konyagin's lower bound [Ko04] (solved): f(N) ≫ (log log N)(log N)². For all large N
there is an admissible A ⊆ {1, …, N} with |A| ≥ c · log log N · (log N)².
-/
theorem erdos_problem_1109.variants.konyagin_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∀ n ∈ A + A, Squarefree n) ∧
      c * Real.log (Real.log N) * (Real.log N) ^ 2 ≤ (A.card : ℝ) :=
  sorry

/--
Konyagin's upper bound [Ko04] (solved): f(N) ≤ N^{11/15 + o(1)}, i.e. for every ε > 0 and
all large N, every admissible A has log |A| ≤ (11/15 + ε) · log N.
-/
theorem erdos_problem_1109.variants.konyagin_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      Real.log (A.card : ℝ) ≤ (11 / 15 + ε) * Real.log N :=
  sorry
