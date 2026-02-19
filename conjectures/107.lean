import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/--
A finite point set P in ℝ² is in general position if no three of its points
are collinear.
-/
def InGeneralPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
A finite point set S in ℝ² is in convex position if no point of S lies in
the convex hull of the remaining points. Equivalently, every point of S is
an extreme point of the convex hull of S, i.e., the points form the vertices
of a convex polygon.
-/
def InConvexPosition (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
f(n) is the smallest integer m such that any m points in ℝ² in general position
(no three collinear) contain some n points in convex position (forming the
vertices of a convex n-gon).
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = m →
    InGeneralPosition P →
    ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
      Q ⊆ P ∧ Q.card = n ∧ InConvexPosition Q}

/--
Erdős Problem #107 (Happy Ending Conjecture, Erdős-Klein-Szekeres):
Let f(n) be the minimal number of points in ℝ², no three collinear, that
guarantees the existence of n points forming the vertices of a convex n-gon.
The conjecture asserts f(n) = 2^(n-2) + 1 for all n ≥ 3.

The lower bound 2^(n-2) + 1 ≤ f(n) and upper bound f(n) ≤ C(2n-4, n-2) + 1
were proved by Erdős and Szekeres [ErSz35, ErSz60]. Known values: f(4) = 5
(Klein) and f(5) = 9 (Turán-Makai). The conjecture remains open for n ≥ 6.
-/
theorem erdos_problem_107 : ∀ n : ℕ, n ≥ 3 → f n = 2 ^ (n - 2) + 1 :=
  sorry
