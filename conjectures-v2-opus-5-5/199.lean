-- [AI - Claude Opus 5.5]: Erdős Problem 199 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
# Erdős Problem #199

*Source:* [erdosproblems.com/199](https://www.erdosproblems.com/199) (status **DISPROVED**: "This
has been solved in the negative."; captured 2026-02-20). [Er75b] [ErGr79] [ErGr80]

If $A\subset \mathbb{R}$ does not contain a 3-term arithmetic progression then must
$\mathbb{R}\backslash A$ contain an infinite arithmetic progression?

Remarks recorded on the page: the answer is no, as shown by Baumgartner [Ba75] (whose construction
uses the axiom of choice to provide a basis for $\mathbb{R}$ over $\mathbb{Q}$).

## Encoding notes

* The theorem is the negative answer, as the existence of a counterexample set. Progressions have
  nonzero common difference; without that every nonempty set would contain a "progression".
* An infinite progression is one-sided, `a + n·d` for `n : ℕ`; a set meeting every one-sided
  progression meets every two-sided one, so this is the stronger reading of the counterexample.
* Sanity checks (PROVED in Lean): `∅` is not a counterexample, since `ℝ` contains `0, 1, 2, …`.

## References

From the site's `/latex/199` bibliography:
* [Ba75] Baumgartner, James E., _Partitioning vector spaces_. J. Combinatorial Theory Ser. A
  (1975), 231–233.

Erdős's sources:
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310. (Site
  `/latex/656` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/199.lean` (Opus 5.5 review, `opus-5-5-review/199.md`).
-/

/-- A set A ⊆ ℝ contains a 3-term arithmetic progression if there exist
    a, d ∈ ℝ with d ≠ 0 such that a, a + d, a + 2d ∈ A. -/
def HasThreeTermAP (A : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A

/-- A set S ⊆ ℝ contains an infinite arithmetic progression if there exist
    a, d ∈ ℝ with d ≠ 0 such that a + n · d ∈ S for all n : ℕ. -/
def HasInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, (a + ↑n * d) ∈ S

/--
Erdős Problem #199 [Er75b, ErGr79, ErGr80] (DISPROVED):

The original conjecture asked: if A ⊂ ℝ does not contain a 3-term
arithmetic progression, must ℝ \ A contain an infinite arithmetic
progression?

Baumgartner [Ba75] showed the answer is no, using the axiom of choice
to construct a counterexample via a Hamel basis for ℝ over ℚ. (Status: DISPROVED; the statement is
the negative answer.)
-/
theorem erdos_problem_199 :
    ∃ A : Set ℝ, ¬HasThreeTermAP A ∧ ¬HasInfiniteAP Aᶜ := by
  sorry

/-- Sanity check (PROVED in Lean): `ℝ` contains the infinite progression `0, 1, 2, …`. -/
theorem erdos_problem_199.hasInfiniteAP_univ : HasInfiniteAP Set.univ :=
  ⟨0, 1, one_ne_zero, fun _ => Set.mem_univ _⟩

/-- Sanity check (PROVED in Lean): the empty set is not a counterexample, since its complement is
`ℝ`. -/
theorem erdos_problem_199.empty_not_counterexample :
    ¬ (¬HasThreeTermAP (∅ : Set ℝ) ∧ ¬HasInfiniteAP (∅ : Set ℝ)ᶜ) := by
  rintro ⟨-, h⟩
  exact h (by simpa using erdos_problem_199.hasInfiniteAP_univ)
