-- [AI - Claude Sonnet 5.5]: Erdős Problem 153 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-!
# Erdős Problem #153: The mean squared gap of the sumset of a Sidon set

*Source:* [erdosproblems.com/153](https://www.erdosproblems.com/153) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; captured 2026-03-05 as the page and as the tidied problem box, with identical
content; the page shows no edit date, "Formalised statement? Yes", and 2 comments, not captured). [ESS94]

Let $A$ be a finite Sidon set and $A+A=\{s_1<\cdots<s_t\}$. Is it true that
$$\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2 \to \infty$$
as $\lvert A\rvert\to \infty$?

Remark recorded on the page: a similar problem can be asked for infinite Sidon sets.

Tags: sidon sets.

**Status.** OPEN. The mirror (`teorth/erdosproblems`, `b916d95`) has `open` since 2025-08-31, no prize, formalised `yes`
(2026-01-08); upstream's `153.lean` (`df3f12d`) has it as `research open`, in the form
`answer(sorry) ↔ Tendsto f atTop atTop`.

**Encoding.**
* `IsSidonSet` and `sumset` are as in Problem 152.
* `sumSquaredGaps l` is the sum of the squares of the differences of consecutive entries of the list `l`. For the
  sorted list `s` of `A + A`, with `t = s.length`, `variants.sumSquaredGaps_eq_sum` proves in Lean that it is
  `∑ i < t - 1, (s[i+1] - s[i])²`, the page's sum with the index shifted by one. The subtraction is in `ℕ` and exact,
  since the list is sorted ascending.
* The statement says: for every `M` there is `N` such that every Sidon set `A` with `N ≤ |A|` satisfies
  `M * t ≤ sumSquaredGaps s`, that is, the mean squared gap `(1/t) ∑ …` is at least `M`. That is "$\to\infty$ as
  $\lvert A\rvert\to\infty$". Here `t` is `S.length`, which is `|A + A|` (`Finset.length_sort`).
* The asked direction ("yes") is asserted, since the problem is open and the page asks a yes/no question.
* The mean squared gap is at least about $4$ for large $\lvert A\rvert$: by Cauchy–Schwarz it is at least
  $(2D)^2/(t(t-1))$ for $D=\max A-\min A$, and $D\ge n(n-1)/2$ because the $n(n-1)/2$ positive differences of a
  Sidon set are distinct. So the content of the question is the growth beyond a constant. This is not formalized.
* `variants.gaps_zero_one_three`, `gaps_seven` and `gaps_zero_one` evaluate the encoding on concrete sets (the sorted
  sumsets are computed by `variants.sort_eq_of_list`). An exact search over the Sidon sets of size `n` with
  `min A = 0` gives the least mean squared gap, for `n = 2, …, 8`, $2/3, 4/3, 9/5, 14/5, 74/21, 9/2, 11/2$, and the
  seven-element minimiser is the one of `gaps_seven`.
* The remark on infinite Sidon sets is not formalized. **DEFERRED:** its precise meaning. Upstream leaves it as a TODO.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From
  upstream's docstring. **DEFERRED:** there is no `/latex/153` fetch in the session logs, so the page's own
  bibliography was not seen.)
-/

/--
A finite set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are
distinct: whenever a + b = c + d with a, b, c, d ∈ A, then
{a, b} = {c, d}.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
The sumset A + A of a finite set A ⊆ ℕ.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
Given a sorted list of natural numbers, compute the sum of squared consecutive
gaps: Σᵢ (sᵢ₊₁ - sᵢ)².
-/
def sumSquaredGaps : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)

/--
Erdős Problem #153 [ESS94] (OPEN):

Let A be a finite Sidon set and A + A = {s₁ < ⋯ < sₜ}. Is it true that
  (1/t) · Σᵢ (sᵢ₊₁ - sᵢ)² → ∞
as |A| → ∞?

Formally: for every M ≥ 1, there exists N such that for every Sidon set A
with |A| ≥ N, if A + A is sorted into a list s of length t, then
  sumSquaredGaps(s) ≥ M * t.
-/
theorem erdos_problem_153 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ (A : Finset ℕ),
      IsSidonSet A →
      N ≤ A.card →
      let S := (sumset A).sort (· ≤ ·)
      M * S.length ≤ sumSquaredGaps S :=
  sorry

/-- Being a Sidon set is decidable (used to evaluate the examples below by `decide`). -/
instance (A : Finset ℕ) : Decidable (IsSidonSet A) := by
  unfold IsSidonSet; infer_instance

/--
`sumSquaredGaps` is the page's sum (PROVED in Lean): for a list `l` it is `∑ i < l.length - 1, (l[i+1] - l[i])²`, with
the entries read by `getD`.
-/
theorem erdos_problem_153.variants.sumSquaredGaps_eq_sum (l : List ℕ) :
    sumSquaredGaps l =
      ∑ i ∈ Finset.range (l.length - 1), (l.getD (i + 1) 0 - l.getD i 0) ^ 2 := by
  induction l with
  | nil => simp [sumSquaredGaps]
  | cons a rest ih =>
    cases rest with
    | nil => simp [sumSquaredGaps]
    | cons b rest' =>
      simp only [sumSquaredGaps]
      rw [ih]
      have hlen : (a :: b :: rest').length - 1 = (b :: rest').length - 1 + 1 := by simp
      rw [hlen, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add]
      exact add_comm _ _

/-- A finset equal to the set of a nodup sorted list sorts to that list (PROVED in Lean). Used to evaluate
`Finset.sort` on concrete sets, which `decide` cannot unfold. -/
theorem erdos_problem_153.variants.sort_eq_of_list (A : Finset ℕ) (l : List ℕ) (hl : l.Nodup)
    (hs : l.Pairwise (· ≤ ·)) (h : A = l.toFinset) : A.sort (· ≤ ·) = l := by
  subst h
  exact (List.toFinset_sort (· ≤ ·) hl).mpr hs

/-- The sumset of `{0, 1, 3}` sorts to `[0, 1, 2, 3, 4, 6]` (PROVED in Lean). -/
theorem erdos_problem_153.variants.sorted_zero_one_three :
    (sumset {0, 1, 3}).sort (· ≤ ·) = [0, 1, 2, 3, 4, 6] :=
  erdos_problem_153.variants.sort_eq_of_list _ _ (by decide) (by decide) (by decide)

/-- `{0, 1, 3}` gives `t = 6` and `∑ gaps² = 8`, a mean squared gap of `4/3` (PROVED in Lean). -/
theorem erdos_problem_153.variants.gaps_zero_one_three :
    ((sumset {0, 1, 3}).sort (· ≤ ·)).length = 6 ∧
      sumSquaredGaps ((sumset {0, 1, 3}).sort (· ≤ ·)) = 8 := by
  rw [erdos_problem_153.variants.sorted_zero_one_three]
  decide

/-- A Sidon set with seven elements and mean squared gap `126/28 = 9/2` (PROVED in Lean). By an exact search this
is the least possible for seven elements with `max A ≤ 80`. -/
theorem erdos_problem_153.variants.gaps_seven :
    IsSidonSet {0, 1, 4, 10, 18, 23, 25} ∧
      ((sumset {0, 1, 4, 10, 18, 23, 25}).sort (· ≤ ·)).length = 28 ∧
      sumSquaredGaps ((sumset {0, 1, 4, 10, 18, 23, 25}).sort (· ≤ ·)) = 126 := by
  have h : (sumset {0, 1, 4, 10, 18, 23, 25}).sort (· ≤ ·) =
      [0, 1, 2, 4, 5, 8, 10, 11, 14, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 33, 35, 36, 41,
        43, 46, 48, 50] :=
    erdos_problem_153.variants.sort_eq_of_list _ _ (by decide) (by decide) (by decide)
  rw [h]
  refine ⟨by decide, by decide, by decide⟩

/-- "Sufficiently large" is needed: for `A = {0, 1}` the mean squared gap is `2/3 < 1` (PROVED in Lean). -/
theorem erdos_problem_153.variants.gaps_zero_one :
    ¬ (1 * ((sumset {0, 1}).sort (· ≤ ·)).length ≤
      sumSquaredGaps ((sumset {0, 1}).sort (· ≤ ·))) := by
  have h : (sumset {0, 1}).sort (· ≤ ·) = [0, 1, 2] :=
    erdos_problem_153.variants.sort_eq_of_list _ _ (by decide) (by decide) (by decide)
  rw [h]
  decide
