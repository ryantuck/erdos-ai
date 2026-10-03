-- [AI - Claude Opus 5.5]: Erdős Problem 102 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Sqrt

open Filter

/-!
# Erdős Problem #102

*Source:* [erdosproblems.com/102](https://www.erdosproblems.com/102) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the
tidied problem box). [Er92e] [Er95] [Er97c]

Let $c > 0$ and $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ such that there are
$\ge c n^2$ lines each containing more than three points, there must be some line containing
$h_c(n)$ many points. Estimate $h_c(n)$. Is it true that, for fixed $c > 0$, we have
$h_c(n) \to \infty$?

Remarks recorded on the page:
* A problem of Erdős and Purdy. It is not even known whether $h_c(n) \ge 5$ (see #101).
* It is easy to see that $h_c(n) \ll_c n^{1/2}$. Erdős [Er95] suggested that perhaps
  $h_c(n) \gg_c n^{1/2}$. Zach Hunter pointed out that this is false, even with $> k$
  points on each line in place of $> 3$. The points of $\{1, \ldots, m\}^d$, with
  $n \approx m^d$, meet any line in $\ll_d n^{1/d}$ points and have $\gg_d n^2$ pairs each
  determining a line with at least $k$ points; a random projection into $\mathbb{R}^2$
  preserves this. The construction shows $h_c(n) \ll n^{1/\log(1/c)}$.

**Encoding.** $h_c(n)$ is the minimum, over admissible $n$-point sets, of the largest number of
points on a line. "$h_c(n) \to \infty$" says: for every $M$, eventually every admissible set
has a line with $\ge M$ points. That is `erdos_problem_102`.

Each pair of points lies on exactly one line, and a line with $\ge 4$ points carries
$\ge \binom42 = 6$ pairs. So there are at most $\binom{n}{2}/6 < n^2/12$ such lines, and for
$c \ge 1/12$ no set is admissible. Both the source question and the Lean statement are then vacuous, so
only small $c$ matter.

Tags: geometry.

## References

* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.

(Provenance: the original pipeline's `/latex` extractions for sibling problems: 94 for
[Er92e] and [Er97c], and 75/843 for [Er95]. They agree with upstream formal-conjectures.)
-/

/--
The number of distinct affine lines in ℝ² that contain at least 4 points from P
(i.e., more than 3 points, as in the problem statement).
-/
noncomputable def fourPlusRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #102 (Erdős–Purdy, OPEN):

For fixed c > 0, let h_c(n) denote the largest integer h such that: for every
n-point set P in ℝ² with at least c·n² lines each containing more than 3 points
of P, some line contains at least h points of P. (In other words, h_c(n) is the
minimum, over all such configurations P, of the maximum collinearity.)

The conjecture is that h_c(n) → ∞ as n → ∞, i.e., for each fixed c > 0 and
each M : ℕ, there exists N such that for all n ≥ N, every n-point configuration
with at least c·n² four-rich lines must contain some line with at least M points.
-/
theorem erdos_problem_102 :
  ∀ c : ℝ, c > 0 →
    ∀ M : ℕ,
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
          ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
            Module.finrank ℝ L.direction = 1 ∧
            M ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} :=
  sorry

/--
"It is not even known whether $h_c(n) \ge 5$" (OPEN): the case `M = 5` of `erdos_problem_102`.
It is equivalent to Problem #101. Every set with no five collinear points has $o(n^2)$
four-point lines if and only if, for every $c > 0$, large sets with $\ge c n^2$ such lines have
a line with $\ge 5$ points.
-/
theorem erdos_problem_102.variants.five :
  ∀ c : ℝ, c > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
        ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ L.direction = 1 ∧
          5 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} :=
  sorry

/--
"It is easy to see that $h_c(n) \ll_c n^{1/2}$" (PROVED, via grids): for all small enough
$c > 0$ and all large $n$, some admissible $n$-point set has at most $C\sqrt n$ points on
every line.
-/
theorem erdos_problem_102.variants.upper_sqrt :
    ∃ c₀ : ℝ, c₀ > 0 ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n ∧ c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) ∧
        ∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ L.direction = 1 →
          (Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} : ℝ) ≤
            C * Real.sqrt n :=
  sorry

/--
Erdős's suggestion $h_c(n) \gg_c n^{1/2}$ is false (PROVED; Hunter's construction with $d = 3$
gives $h_c(n) \ll n^{1/3}$ for some $c > 0$ and infinitely many $n$).
-/
theorem erdos_problem_102.variants.not_sqrt_lower :
    ¬ ∀ c : ℝ, c > 0 → ∃ C : ℝ, C > 0 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        c * (n : ℝ) ^ 2 ≤ (fourPlusRichLineCount P : ℝ) →
        ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ L.direction = 1 ∧
          C * Real.sqrt n ≤
            (Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} : ℝ) :=
  sorry
