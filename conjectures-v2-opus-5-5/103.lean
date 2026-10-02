-- [AI - Claude Opus 5.5]: Erdős Problem 103 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Erdős Problem #103

*Source:* [erdosproblems.com/103](https://www.erdosproblems.com/103) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the
tidied problem box). [Er94b]

Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimise
the diameter subject to the constraint that $d(x,y) \ge 1$ for all points $x \ne y$. Is it
true that $h(n) \to \infty$?

Remarks recorded on the page: it is not even known whether $h(n) \ge 2$ for all large $n$.
See also Problem #99.

**Encoding.** `h n` counts congruence classes with `Set.encard`, valued in `ℕ∞`, so an
infinite family of incongruent minimisers counts as `⊤`. The first pass used `Set.ncard`,
which returns `0` for an infinite set. That case is not hypothetical: a minimiser with a
"rattler" (a point that can move freely without breaking a constraint or changing the
diameter) produces a continuum of incongruent minimisers. With `ncard` the statement would
then fail at such `n`, even though the informal $h(n)$ is infinite there.

Tags: geometry, distances. OEIS: "possible".

## References

* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.

(Provenance: the original pipeline's `/latex/106` and `/latex/755` extractions. They agree
with upstream formal-conjectures.)
-/

/--
A finite set of points in ℝ² is unit-separated if all pairwise distances
between distinct points are at least 1.
-/
def IsUnitSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1

/--
The diameter of a finite set of points in ℝ²: the supremum of all pairwise distances.
-/
noncomputable def finiteDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sSup {d : ℝ | ∃ p ∈ A, ∃ q ∈ A, d = dist p q}

/--
A configuration of n points in ℝ² minimizes the diameter among all unit-separated
n-point configurations: it is unit-separated, and no other unit-separated n-point set
has strictly smaller diameter.
-/
def IsMinimalDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsUnitSeparated A ∧
  ∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
    B.card = A.card → IsUnitSeparated B → finiteDiameter A ≤ finiteDiameter B

/--
Two finite point sets in ℝ² are congruent if there is an isometric equivalence of ℝ²
mapping one to the other (i.e., one can be obtained from the other by a rigid motion).
-/
def AreCongruent (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
    A.image (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = B

/--
h(n) counts the number of congruence classes of minimal-diameter unit-separated
n-point configurations in ℝ². That is, it counts the number of incongruent sets
of n points that minimize the diameter subject to d(x,y) ≥ 1 for all x ≠ y.

The congruence classes are the equivalence classes of the set of all
minimal-diameter unit-separated n-point configurations under congruence. They are counted
with `Set.encard`, so infinitely many classes give `⊤`, not the junk value `0` that
`Set.ncard` would give.
-/
noncomputable def h (n : ℕ) : ℕ∞ :=
  let minimizers : Set (Finset (EuclideanSpace ℝ (Fin 2))) :=
    {A | A.card = n ∧ IsMinimalDiameter A}
  Set.encard {C : Set (Finset (EuclideanSpace ℝ (Fin 2))) |
    ∃ A ∈ minimizers, C = minimizers ∩ {B | AreCongruent A B}}

/--
Erdős Problem #103 (OPEN):
Let h(n) count the number of incongruent sets of n points in ℝ² which minimize
the diameter subject to the constraint that d(x,y) ≥ 1 for all distinct points
x, y. The conjecture is that h(n) → ∞ as n → ∞; here `h n = ⊤` (infinitely many
classes) counts as large.

It is not even known whether h(n) ≥ 2 for all sufficiently large n.
-/
theorem erdos_problem_103 : ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (M : ℕ∞) ≤ h n :=
  sorry

/--
The weaker question from the page (OPEN): is $h(n) \ge 2$ for all large $n$?
-/
theorem erdos_problem_103.variants.at_least_two : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ≤ h n :=
  sorry
