-- [AI - Claude Sonnet 5.5]: Erdős Problem 141 — second-pass formalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

open Nat

/-!
# Erdős Problem #141: Consecutive Primes in Arithmetic Progression

*Source:* [erdosproblems.com/141](https://www.erdosproblems.com/141) (banner **OPEN**: "This is open,
and cannot be resolved with a finite computation."; page last edited 28 September 2025; captured
2026-03-05 as the tidied problem box). [Er75b] [Er83] [Er97c]

Let $k\geq 3$. Are there $k$ consecutive primes in arithmetic progression?

Remarks recorded on the page:
* Green and Tao [GrTa08] have proved that there must always exist some $k$ primes in arithmetic
  progression, but these need not be consecutive. Erdős called this conjecture "completely hopeless at
  present".
* The existence of such progressions for small $k$ has been verified for $k\leq 10$, see the Wikipedia
  page. It is open, even for $k=3$, whether there are infinitely many such progressions.
* See also [219]. This is discussed in problem A6 of Guy's collection [Gu04].

Tags: additive combinatorics, primes, arithmetic progressions. OEIS: A006560. 4 comments at capture
(not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31. Upstream has
`erdos_141 : answer(sorry) ↔ ∀ k ≥ 3, ∃ s, s.IsAPAndPrimeProgressionOfLength k`, category
`research open`.

**Encoding.**
* The main theorem asserts "yes for every $k\ge3$", the asked direction while the problem is open: for
  every `k ≥ 3` there are `a` and `d > 0` such that `a, a + d, …, a + (k - 1) * d` are all prime and no
  prime lies strictly between consecutive terms. The terms are then `k` consecutive primes. The first
  term is `a` itself, and `d > 0` makes the progression increasing.
* `IsConsecutivePrimeAP k a d` is that condition for given `k`, `a`, `d`, and `variants.main_iff` shows
  that the main theorem says `∀ k ≥ 3, ∃ a d, IsConsecutivePrimeAP k a d`.
* The page asks the question for a given `k`. The ∀-form is the conjunction of the questions, and it is
  also what upstream states.
* `variants.three`, `variants.four`, `variants.five` and `variants.six` prove in Lean the cases $k=3,4,5,6$,
  with the smallest examples $(3,2)$, $(251,6)$, $(9843019,30)$ and $(121174811,30)$. They show that the
  encoding accepts real progressions. `variants.first_cases` is the page's $k\le10$.
* `variants.infinite_three` is the page's open question for $k=3$. `variants.green_tao` is the theorem of
  [GrTa08], and `variants.green_tao_of_main` shows that the main theorem implies it.

## References

* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques de
  Bordeaux (Conf., Univ. Bordeaux, 1974) (1975), 295–310.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.
* [GrTa08] Green, B. and Tao, T. (2008), the theorem that the primes contain arbitrarily long arithmetic
  progressions. **DEFERRED:** the title and venue were not recovered.
* [Er83] cited on the page. **DEFERRED:** no bibliographic data was recovered.
* [219] The page's cross-reference to Problem 219.
* The Wikipedia article "Primes in arithmetic progression", section "Consecutive primes in arithmetic
  progression", which the page links.

(Provenance: [Er75b], [Er97c] and [Gu04] are from the bibliographies of the `/latex` pages of other
problems. **DEFERRED:** no `/latex/141` fetch exists in the logs, so the entries were not checked against
the page's own bibliography.)
-/

/-- `k` consecutive primes `a, a + d, …, a + (k - 1) * d` form an arithmetic progression with common
    difference `d > 0`: all terms are prime and no prime lies strictly between consecutive terms. -/
def IsConsecutivePrimeAP (k a d : ℕ) : Prop :=
  0 < d ∧
    (∀ i : ℕ, i < k → Nat.Prime (a + i * d)) ∧
    (∀ i : ℕ, i + 1 < k →
      ∀ p : ℕ, a + i * d < p → p < a + (i + 1) * d → ¬ Nat.Prime p)

/--
Erdős Problem #141 [Er75b, Er83, Er97c] — OPEN:
Let k ≥ 3. Are there k consecutive primes in arithmetic progression?

That is, for every k ≥ 3, there exist a first prime a and common difference d > 0
such that a, a + d, a + 2d, ..., a + (k-1)d are all prime and consecutive
(no prime lies strictly between a + i*d and a + (i+1)*d for each i).

Green and Tao proved that there always exist k primes in arithmetic progression,
but these need not be consecutive. Verified for k ≤ 10.
-/
theorem erdos_problem_141 :
    ∀ k : ℕ, 3 ≤ k →
    ∃ a d : ℕ, 0 < d ∧
      (∀ i : ℕ, i < k → Nat.Prime (a + i * d)) ∧
      (∀ i : ℕ, i + 1 < k →
        ∀ p : ℕ, a + i * d < p → p < a + (i + 1) * d → ¬ Nat.Prime p) :=
  sorry

/-- The main theorem is `∀ k ≥ 3, ∃ a d, IsConsecutivePrimeAP k a d` (PROVED in Lean). -/
theorem erdos_problem_141.variants.main_iff :
    (∀ k : ℕ, 3 ≤ k →
      ∃ a d : ℕ, 0 < d ∧
        (∀ i : ℕ, i < k → Nat.Prime (a + i * d)) ∧
        (∀ i : ℕ, i + 1 < k →
          ∀ p : ℕ, a + i * d < p → p < a + (i + 1) * d → ¬ Nat.Prime p)) ↔
    ∀ k : ℕ, 3 ≤ k → ∃ a d : ℕ, IsConsecutivePrimeAP k a d :=
  Iff.rfl

/-- $k=3$: the primes $3, 5, 7$ (PROVED in Lean). -/
theorem erdos_problem_141.variants.three : ∃ a d : ℕ, IsConsecutivePrimeAP 3 a d := by
  refine ⟨3, 2, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi p h1 h2
    have hi' : i < 2 := by omega
    interval_cases i
    all_goals norm_num at h1 h2
    all_goals (interval_cases p; all_goals norm_num)

/-- $k=4$: the primes $251, 257, 263, 269$ (PROVED in Lean). -/
theorem erdos_problem_141.variants.four : ∃ a d : ℕ, IsConsecutivePrimeAP 4 a d := by
  refine ⟨251, 6, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi p h1 h2
    have hi' : i < 3 := by omega
    interval_cases i
    all_goals norm_num at h1 h2
    all_goals (interval_cases p; all_goals norm_num)

/-- $k=5$: the primes $9843019, 9843049, \dots, 9843139$ (PROVED in Lean). -/
theorem erdos_problem_141.variants.five : ∃ a d : ℕ, IsConsecutivePrimeAP 5 a d := by
  refine ⟨9843019, 30, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi p h1 h2
    have hi' : i < 4 := by omega
    interval_cases i
    all_goals norm_num at h1 h2
    all_goals (interval_cases p; all_goals norm_num)

/-- $k=6$: the primes $121174811, 121174841, \dots, 121174961$ (PROVED in Lean). -/
theorem erdos_problem_141.variants.six : ∃ a d : ℕ, IsConsecutivePrimeAP 6 a d := by
  refine ⟨121174811, 30, by norm_num, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num
  · intro i hi p h1 h2
    have hi' : i < 5 := by omega
    interval_cases i
    all_goals norm_num at h1 h2
    all_goals (interval_cases p; all_goals norm_num)

/--
The page's computation (PROVED by computer search per the page, not checked here): such progressions
exist for every `3 ≤ k ≤ 10`. The cases `k ≤ 6` are proved in Lean above.
-/
theorem erdos_problem_141.variants.first_cases :
    ∀ k : ℕ, 3 ≤ k → k ≤ 10 → ∃ a d : ℕ, IsConsecutivePrimeAP k a d :=
  sorry

/--
The page's open question for `k = 3` (OPEN): are there infinitely many progressions of three
consecutive primes? A progression is determined by its first term, so this asks whether infinitely
many first terms `a` occur.
-/
theorem erdos_problem_141.variants.infinite_three :
    Set.Infinite {a : ℕ | ∃ d : ℕ, IsConsecutivePrimeAP 3 a d} :=
  sorry

/--
Green and Tao [GrTa08] (PROVED, not checked here): for every `k` there are `k` primes in arithmetic
progression with positive common difference, not necessarily consecutive.
-/
theorem erdos_problem_141.variants.green_tao :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → Nat.Prime (a + i * d) :=
  sorry

/--
The main theorem implies the theorem of Green and Tao (PROVED in Lean): `k` consecutive primes in
arithmetic progression are in particular `k` primes in arithmetic progression, and `max k 3`
consecutive primes contain `k` of them.
-/
theorem erdos_problem_141.variants.green_tao_of_main
    (hmain : ∀ k : ℕ, 3 ≤ k → ∃ a d : ℕ, IsConsecutivePrimeAP k a d) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → Nat.Prime (a + i * d) := by
  intro k
  obtain ⟨a, d, hd, hp, -⟩ := hmain (max k 3) (le_max_right _ _)
  exact ⟨a, d, hd, fun i hi => hp i (lt_of_lt_of_le hi (le_max_left _ _))⟩
