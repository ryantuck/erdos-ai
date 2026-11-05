-- [AI - Claude Opus 5.5]: Erdős Problem 194 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem #194

*Source:* [erdosproblems.com/194](https://www.erdosproblems.com/194) (status **DISPROVED**: "This
has been solved in the negative."; captured 2026-03-05). [ErGr79] [ErGr80]

Let $k\geq 3$. Must any ordering of $\mathbb{R}$ contain a monotone $k$-term arithmetic
progression, that is, some $x_1<\cdots<x_k$ which forms an increasing or decreasing $k$-term
arithmetic progression?

Remarks recorded on the page: the answer is no, even for $k=3$, as shown by Ardal, Brown, and
Jungić [ABJ11]. See also [195] and [196].

## Encoding notes

* The theorem states the answer as a direct assertion: some strict total order on `ℝ` has no
  monotone 3-term progression, i.e. for every progression `a, a+d, a+2d` (`d ≠ 0`, either sign) the
  middle term is not between the two ends in the order.
* `k = 3` settles every `k ≥ 3`: the first three terms of a monotone `k`-term progression form a
  monotone 3-term progression (`variants.all_k`, PROVED in Lean).
* The usual order of `ℝ` is not an example (`variants.usual_order`, PROVED), so the statement is
  not trivial.

## References

No `/latex/194` fetch is in the session logs.
* [ABJ11] Ardal, H., Brown, T. and Jungić, V., _Chaotic orderings of the rationals and reals_.
  Amer. Math. Monthly (2011), 921–925. (From upstream `formal-conjectures`, `2befc3a`;
  **DEFERRED** as a site entry.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/194.lean` (Opus 5.5 review, `opus-5-5-review/194.md`).
-/

/--
Erdős Problem #194 [ErGr79, ErGr80]:

Let k ≥ 3. Must any linear ordering of ℝ contain a monotone k-term arithmetic
progression, that is, some x₁ < ⋯ < xₖ (in the ordering) which forms an
increasing or decreasing k-term arithmetic progression in the usual order?

The answer is no, even for k = 3, as shown by Ardal, Brown, and Jungić [ABJ11].
Formally: there exists a strict total order on ℝ such that no 3-term arithmetic
progression is monotone with respect to it. (Status: DISPROVED; the statement is the true
direction, the negative answer.)
-/
theorem erdos_problem_194 :
    ∃ (r : ℝ → ℝ → Prop) (_ : IsStrictTotalOrder ℝ r),
      ∀ (a d : ℝ), d ≠ 0 →
        ¬((r a (a + d) ∧ r (a + d) (a + 2 * d)) ∨
          (r (a + 2 * d) (a + d) ∧ r (a + d) a)) :=
  sorry

/-- The relation `r` orders the `k`-term progression `a, a + d, …, a + (k-1)d` monotonically:
consecutive terms increase, or all decrease, in `r`. -/
def IsMonotoneAP194 (r : ℝ → ℝ → Prop) (k : ℕ) (a d : ℝ) : Prop :=
  (∀ i : ℕ, i + 1 < k → r (a + i * d) (a + (i + 1) * d)) ∨
    (∀ i : ℕ, i + 1 < k → r (a + (i + 1) * d) (a + i * d))

/-- `k = 3` settles every `k ≥ 3` (PROVED in Lean): if no 3-term progression is monotone for `r`,
then no `k`-term progression is, for any `k ≥ 3`. -/
theorem erdos_problem_194.variants.all_k (r : ℝ → ℝ → Prop)
    (h : ∀ (a d : ℝ), d ≠ 0 →
      ¬((r a (a + d) ∧ r (a + d) (a + 2 * d)) ∨ (r (a + 2 * d) (a + d) ∧ r (a + d) a)))
    (k : ℕ) (hk : 3 ≤ k) (a d : ℝ) (hd : d ≠ 0) : ¬ IsMonotoneAP194 r k a d := by
  rintro (hup | hdown)
  · have h0 := hup 0 (by omega)
    have h1 := hup 1 (by omega)
    norm_num at h0 h1
    exact h a d hd (Or.inl ⟨h0, h1⟩)
  · have h0 := hdown 0 (by omega)
    have h1 := hdown 1 (by omega)
    norm_num at h0 h1
    exact h a d hd (Or.inr ⟨h1, h0⟩)

/-- The usual order of `ℝ` is not an example (PROVED in Lean): `0 < 1 < 2` is a monotone
progression. -/
theorem erdos_problem_194.variants.usual_order :
    ¬ ∀ (a d : ℝ), d ≠ 0 →
      ¬(((a < a + d) ∧ (a + d < a + 2 * d)) ∨ ((a + 2 * d < a + d) ∧ (a + d < a))) := by
  intro h
  exact h 0 1 one_ne_zero (Or.inl ⟨by norm_num, by norm_num⟩)
