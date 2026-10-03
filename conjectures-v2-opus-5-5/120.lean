-- [AI - Claude Opus 5.5]: Erdős Problem 120 — second-pass formalization
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

open MeasureTheory Set Filter Topology

/-!
# Erdős Problem #120: The Erdős Similarity Problem

*Source:* [erdosproblems.com/120](https://www.erdosproblems.com/120) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; prize \$100; captured 2026-02-20
and 2026-03-05 as the tidied problem box). [Er74b] [Er81b, p.29] [Er83d] [Er90] [Er97f]
[Va99, 2.46]

Let $A\subseteq\mathbb{R}$ be an infinite set. Must there be a set $E\subset \mathbb{R}$ of
positive measure which does not contain any set of the shape $aA+b$ for some $a,b\in\mathbb{R}$
and $a\neq 0$?

Remarks recorded on the page:
* The Erdős similarity problem.
* This is true if $A$ is unbounded or dense in some interval. It therefore suffices to prove
  this when $A=\{a_1>a_2>\cdots\}$ is a countable strictly monotone sequence which converges
  to $0$.
* Steinhaus [St20] has proved this is false whenever $A$ is a finite set.
* This conjecture is known in many special cases. But, for example, it is open when
  $A=\{1,1/2,1/4,\ldots\}$, which is Problem 94 on Green's open problems list. For an overview
  of progress, the page recommends a survey by Svetic [Sv00]; a survey of more recent progress
  was written by Jung, Lai, and Mooroogen [JLM24].

**Encoding.**
* "Positive measure" is `volume E ≠ 0` in `ℝ≥0∞`.
* `MeasurableSet` means Borel measurable. That loses nothing: a Lebesgue-measurable $E$ of
  positive measure contains a compact $F$ of positive measure, and $F$ avoids every affine
  copy that $E$ avoids.
* `erdos_problem_120` asserts the conjectured ("yes") direction, as the problem is open.
* `AvoidsAffineCopies` names the property for use in the variants. The main theorem keeps
  the first pass's inline statement.

Tags: combinatorics.

## References

* [Er74b] Erdős, P., _Remarks on some problems in number theory_. Math. Balkanica (1974),
  197–202.
* [Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981), 27–35.
* [Er83d] Erdős, P. (1983). Bibliographic details not recovered (DEFERRED).
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. (Problem 2.46.)
* [St20] Steinhaus, H., _Sur les distances des points dans les ensembles de mesure positive_.
  Fund. Math. (1920), 93–104.
* [Sv00] Svetic (2000), a survey of the Erdős similarity problem. Details not recovered
  (DEFERRED).
* [JLM24] Jung, Lai and Mooroogen (2024), a survey of recent progress. Details not recovered
  (DEFERRED).

(Provenance: no `/latex/120` fetch exists in the session logs. [Er74b], [Er81b], [Er90],
[Er97f] and [Va99] are from sibling `/latex` extractions. [St20] is from upstream `120.lean`,
whose title has "measure" where "mesure" is meant. [Er83d], [Sv00] and [JLM24] are known only
by key and by the page's text.)
-/

/--
Erdős Problem #120 (The Erdős Similarity Problem) [Er74b, Er81b, Er83d, Er90, Er97f]:

Let A ⊆ ℝ be an infinite set. Must there be a set E ⊂ ℝ of positive Lebesgue measure
which does not contain any set of the shape aA + b for some a, b ∈ ℝ with a ≠ 0?

In other words, for every infinite A ⊆ ℝ, there exists a measurable set E with
μ(E) > 0 such that no affine copy of A is contained in E.

This is known to be true when A is unbounded or dense in some interval. Steinhaus [St20]
proved it is false whenever A is a finite set.
-/
theorem erdos_problem_120 :
    ∀ A : Set ℝ, A.Infinite →
      ∃ E : Set ℝ, MeasurableSet E ∧
        volume E ≠ 0 ∧
        ∀ a b : ℝ, a ≠ 0 →
          ¬((fun x => a * x + b) '' A ⊆ E) :=
  sorry

/-- `A` admits a measurable set of positive measure that contains no affine copy
    `aA + b` (`a ≠ 0`) of `A`. This is the conclusion of `erdos_problem_120`. -/
def AvoidsAffineCopies (A : Set ℝ) : Prop :=
  ∃ E : Set ℝ, MeasurableSet E ∧ volume E ≠ 0 ∧
    ∀ a b : ℝ, a ≠ 0 → ¬((fun x => a * x + b) '' A ⊆ E)

/--
Unbounded sets (PROVED; elementary): every affine copy of an unbounded `A` is unbounded, so a
bounded interval of positive length avoids all of them.
-/
theorem erdos_problem_120.variants.unbounded :
    ∀ A : Set ℝ, ¬ (BddAbove A ∧ BddBelow A) → AvoidsAffineCopies A :=
  sorry

/--
Sets dense in an interval (PROVED). Take `E` closed, nowhere dense, of positive measure (a
fat Cantor set). An affine copy dense in an interval would force the closed set `E` to
contain that interval.
-/
theorem erdos_problem_120.variants.dense_in_interval :
    ∀ A : Set ℝ, (∃ u v : ℝ, u < v ∧ Ioo u v ⊆ closure A) → AvoidsAffineCopies A :=
  sorry

/--
Steinhaus [St20] (PROVED): for finite `A`, every measurable set of positive measure contains an
affine copy of `A`. So the infiniteness hypothesis in `erdos_problem_120` is necessary.
-/
theorem erdos_problem_120.variants.steinhaus :
    ∀ A : Set ℝ, A.Finite → ¬ AvoidsAffineCopies A :=
  sorry

/--
The page's reduction (PROVED; elementary). It suffices to treat strictly decreasing sequences
tending to 0. An infinite bounded set contains a strictly monotone sequence converging to some
point, and translation and reflection turn it into such a sequence. Avoiding copies of a
subset avoids copies of the set.
-/
theorem erdos_problem_120.variants.reduction :
    (∀ x : ℕ → ℝ, StrictAnti x → Tendsto x atTop (𝓝 0) → AvoidsAffineCopies (range x)) →
      ∀ A : Set ℝ, A.Infinite → AvoidsAffineCopies A :=
  sorry

/--
The geometric case A = {1, 1/2, 1/4, …} (OPEN; Problem 94 on Green's list), asserted in the
conjectured direction.
-/
theorem erdos_problem_120.variants.geometric :
    AvoidsAffineCopies (range fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
  sorry
