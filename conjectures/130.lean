import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open SimpleGraph

/-- A set of four points in ℝ² is concyclic if they all lie on a common circle
    (i.e., there exist a center O ∈ ℝ² and radius r > 0 such that each of the
    four points is at distance r from O). -/
def Concyclic (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ),
    0 < radius ∧
    dist a center = radius ∧
    dist b center = radius ∧
    dist c center = radius ∧
    dist d center = radius

/-- A point set A ⊆ ℝ² is in Erdős general position if no three distinct points
    of A are collinear, and no four distinct points of A are concyclic. -/
def ErdosGeneralPosition (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A →
    p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  (∀ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A → s ∈ A →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬Concyclic p q r s)

/-- The integer-distance graph on a point set A ⊆ ℝ²: vertices are points of A,
    and two distinct points are adjacent if and only if their Euclidean distance
    is a positive integer. -/
noncomputable def intDistGraph (A : Set (EuclideanSpace ℝ (Fin 2))) :
    SimpleGraph ↥A where
  Adj p q := (p : EuclideanSpace ℝ (Fin 2)) ≠ q ∧
    ∃ n : ℕ, 0 < n ∧ dist (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 2)) = n
  symm := fun _p _q ⟨hne, n, hn, hd⟩ => ⟨hne.symm, n, hn, by rw [dist_comm]; exact hd⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/--
Erdős Problem #130 [Er97b] (asked by Andrásfai and Erdős):
Let A ⊆ ℝ² be an infinite set with no three points collinear and no four points
concyclic. Consider the integer-distance graph G on A, where two distinct points
are adjacent if and only if their Euclidean distance is a positive integer.

How large can the chromatic number and clique number of G be? In particular,
can the chromatic number be infinite?

This conjecture states YES: there exists such a set A for which the
integer-distance graph has infinite chromatic number.

Note: The clique number is always finite. The Anning–Erdős theorem [AnEr45]
shows that any infinite set of points in the plane with all pairwise integer
distances must be collinear; since A has no three collinear points, A contains
no infinite complete subgraph. Hence arbitrarily large finite chromatic number
(or infinite chromatic number) would be an example of a graph with finite
clique number and infinite chromatic number.
-/
theorem erdos_problem_130 :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))),
      A.Infinite ∧ ErdosGeneralPosition A ∧
      (intDistGraph A).chromaticNumber = ⊤ :=
  sorry
