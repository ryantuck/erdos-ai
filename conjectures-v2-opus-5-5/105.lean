-- [AI - Claude Opus 5.5]: Erdős Problem 105 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #105

*Source:* [erdosproblems.com/105](https://www.erdosproblems.com/105) (status
**DISPROVED (LEAN)**, \$50: "This has been solved in the negative and the proof verified in
Lean."; page last edited 25 October 2025, captured 2026-02-19). [Er95] [ErPu95]

Let $A, B \subset \mathbb{R}^2$ be disjoint sets of size $n$ and $n-3$ respectively, with not
all of $A$ contained on a single line. Is there a line which contains at least two points from
$A$ and no points from $B$?

Remarks recorded on the page:
* Conjectured by Erdős and Purdy [ErPu95]; the prize is for a proof or a disproof.
* A construction of Hickerson shows that this fails with $n - 2$.
* A result proved independently by Beck [Be83] and by Szemerédi and Trotter [SzTr83] (see
  #211) implies that it is true with $n - 3$ replaced by $cn$ for some constant $c > 0$.
* This has been disproved by Xichuan in the page's comments, with three explicit
  counterexamples. It remains possible that it holds with $n - 4$, or in general with
  $n - O(1)$ or $(1 - o(1))n$.

**Polarity.** The question has been answered "no", so `erdos_problem_105` asserts the negation
of the first-pass statement. The first-pass statement, the "yes" direction, was false as an
assertion.

Tags: geometry.

## References

* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [ErPu95] Erdős, P. and Purdy, G., _Two combinatorial problems in the plane_. Discrete
  Comput. Geom. (1995), 441–443.
* [Be83] Beck, J., _On the lattice property of the plane and some problems of Dirac, Motzkin
  and Erdős in combinatorial geometry_. Combinatorica (1983), 281–297.
* [SzTr83] Szemerédi, E. and Trotter, W. T., Jr., _Extremal problems in discrete geometry_.
  Combinatorica (1983), 381–392.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/105` gives the authors,
titles and journals of [ErPu95], [Be83] and [SzTr83]. The [SzTr83] pages come from
`/latex/607` and `/latex/1069`. The [ErPu95] and [Be83] pages come from upstream
formal-conjectures `ErdosProblems/105.lean` at `df3f12d`. [Er95] comes from `/latex/75` and
`/latex/843`.)
-/

/--
Some line contains at least two points of `A` and no point of `B`.
-/
def HasCleanLine (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
    Module.finrank ℝ L.direction = 1 ∧
    2 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
    ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ (B : Set _) → p ∉ L

/--
Erdős Problem #105 (Erdős–Purdy, DISPROVED):
It is **not** the case that for all disjoint finite A, B ⊂ ℝ² with |A| = n,
|B| = n - 3 and A not contained in a single line, there is a line containing
at least two points from A and no points from B.

Xichuan found three explicit counterexamples. It remains open whether the result holds with
n - 4 (or more generally with n - O(1) or (1 - o(1))n points in B). The condition n - 2 is
known to fail via a construction of Hickerson. The statement under `¬` is the first-pass
statement, byte for byte.
-/
theorem erdos_problem_105 :
    ¬ (∀ n : ℕ, 3 ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n →
      B.card = n - 3 →
      Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ L.direction = 1 ∧
        2 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (A : Set _) ∧ p ∈ L} ∧
        ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ (B : Set _) → p ∉ L) :=
  sorry

/--
Hickerson (PROVED): the statement also fails with $|B| = n - 2$.
-/
theorem erdos_problem_105.variants.hickerson :
    ¬ (∀ n : ℕ, 2 ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n → B.card = n - 2 → Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      HasCleanLine A B) :=
  sorry

/--
Beck [Be83] and Szemerédi–Trotter [SzTr83] (PROVED; see #211): the statement holds when
$|B| \le c|A|$ for some absolute constant $c > 0$.
-/
theorem erdos_problem_105.variants.beck_szemeredi_trotter :
    ∃ c : ℝ, c > 0 ∧
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      Disjoint A B → (B.card : ℝ) ≤ c * A.card →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      HasCleanLine A B :=
  sorry

/--
Does it hold with $n - 4$? (OPEN.)
-/
theorem erdos_problem_105.variants.n_sub_four :
    ∀ n : ℕ, 4 ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n → B.card = n - 4 → Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      HasCleanLine A B :=
  sorry

/--
Does it hold with $n - O(1)$? (OPEN.) That is, with $|B| = n - k$ for some fixed $k$. This
is implied by `n_sub_four` (take $k = 4$).
-/
theorem erdos_problem_105.variants.n_sub_const :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n → B.card = n - k → Disjoint A B →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      HasCleanLine A B :=
  sorry

/--
Does it hold with $(1 - o(1))n$? (OPEN.) For every $\varepsilon > 0$ and all large $A$, every
disjoint $B$ with $|B| \le (1 - \varepsilon)|A|$ admits a clean line. This is implied by
`n_sub_const`: pad `B` with points outside `A` up to size $n - k$. Adding points to `B` can
only destroy clean lines, so a clean line for the padded set is clean for `B`.
-/
theorem erdos_problem_105.variants.one_sub_o_one :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ,
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      N ≤ A.card → Disjoint A B → (B.card : ℝ) ≤ (1 - ε) * A.card →
      ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))) →
      HasCleanLine A B :=
  sorry
