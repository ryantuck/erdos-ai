-- [AI - Claude Opus 5.5]: Erdős Problem 98 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

open Filter

/-!
# Erdős Problem #98

*Source:* [erdosproblems.com/98](https://www.erdosproblems.com/98) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; page last edited 15 October
2025, captured 2026-02-23). [Er75f, p.101] [Er83c] [Er87b, p.167] [Er90] [Er92b] [EFPR93]
[Er94b] [Er97e]

Let $h(n)$ be such that any $n$ points in $\mathbb{R}^2$, with no three on a line and no
four on a circle, determine at least $h(n)$ distinct distances. Does $h(n)/n \to \infty$?

Remarks recorded on the page:
* Erdős could not even prove $h(n) \ge n$.
* Pach has shown $h(n) < n^{\log_2 3}$.
* Erdős, Füredi and Pach [EFPR93] improved this to $h(n) < n \exp(c \sqrt{\log n})$ for some
  constant $c > 0$.

**Encoding.** $h(n)$ is the minimum number of distinct distances over admissible $n$-point
sets. Such sets exist for every $n$, e.g. generic points. So "$h(n)/n \to \infty$" says: for
every $C$, eventually every admissible $n$-point set has at least $Cn$ distinct distances.
That is `erdos_problem_98`, stated without naming $h$.

Tags: geometry, distances. OEIS: "possible".

## References

* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54.
* [Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive
  geometry (Siófok, 1985) (1987), 167–177.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231–240.
* [EFPR93] Erdős, P., Füredi, Z., Pach, J. and Ruzsa, I. Z., _The grid revisited_. Discrete
  Math. (1993), 189–196.
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.

(Provenance: the original pipeline's `/latex` extractions. `/latex/98` gives the [EFPR93]
authors, `/latex/217` gives [Er83c], `/latex/24` gives [Er92b], and sibling problems give the
rest. All agree with the reference block of upstream formal-conjectures `ErdosProblems/98.lean`
at `df3f12d`, which supplies the [EFPR93] title, venue and pages.)
-/

/--
A finite point set in ℝ² has no three collinear if every three-element subset
is not collinear (i.e., no line contains three or more of the points).
-/
def NoThreeCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
Four points in ℝ² are concyclic if they all lie on a common circle, i.e.,
there exists a center and positive radius such that all four points are
equidistant from the center.
-/
def FourPointsConcyclic (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, dist p c = r

/--
A finite point set in ℝ² has no four concyclic if every four-element subset
does not lie on a common circle.
-/
def NoFourConcyclic (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 4 → ¬FourPointsConcyclic S

/--
The number of distinct pairwise distances determined by a finite point set in ℝ².
-/
noncomputable def distinctDistanceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ dist p q = d}

/--
Erdős Problem #98 (OPEN):
Let h(n) be the minimum number of distinct distances determined by any n points
in ℝ² with no three collinear and no four concyclic. Does h(n)/n → ∞?

Formally: for every C > 0 there exists N such that for all n ≥ N and every
set P of n points in ℝ² with no three collinear and no four concyclic,
the number of distinct distances is at least C · n.
-/
theorem erdos_problem_98 :
  ∀ C : ℝ, C > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoThreeCollinear P →
        NoFourConcyclic P →
        (distinctDistanceCount P : ℝ) ≥ C * (n : ℝ) :=
  sorry

/--
Erdős, Füredi, Pach and Ruzsa [EFPR93] (PROVED): $h(n) < n \exp(c \sqrt{\log n})$. For some
$c > 0$ and every large $n$, some admissible $n$-point set has fewer than
$n \exp(c \sqrt{\log n})$ distinct distances. This improves Pach's $h(n) < n^{\log_2 3}$.
-/
theorem erdos_problem_98.variants.efpr_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n ∧ NoThreeCollinear P ∧ NoFourConcyclic P ∧
        (distinctDistanceCount P : ℝ) < (n : ℝ) * Real.exp (c * Real.sqrt (Real.log (n : ℝ))) :=
  sorry
