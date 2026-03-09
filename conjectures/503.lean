import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Finset

noncomputable section

/--
A finite set of points in ℝ^d is **isosceles** if every three distinct points
from the set determine an isosceles triangle: for any three distinct points
x, y, z, at least two of the distances |x-y|, |y-z|, |x-z| are equal.
-/
def IsIsoscelesSet {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → y ≠ z → x ≠ z →
      dist x y = dist y z ∨ dist y z = dist x z ∨ dist x y = dist x z

/--
The maximum size of an isosceles set in ℝ^d.
-/
def maxIsoscelesSize (d : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n ∧ IsIsoscelesSet A}

/--
Erdős Problem #503 [ErKe47, Er61]:

What is the size of the largest A ⊆ ℝ^d such that every three points from A
determine an isosceles triangle (i.e., for any three points x, y, z from A,
at least two of the distances |x-y|, |y-z|, |x-z| are equal)?

When d = 2 the answer is 6 (Kelly [ErKe47]). When d = 3 the answer is 8
(Croft [Cr62]). Blokhuis [Bl84] proved the upper bound |A| ≤ C(d+2, 2).
Alweiss observed a lower bound of C(d+1, 2), improved by Weisenberg to
C(d+1, 2) + 1.

The conjecture below states the Blokhuis upper bound: every isosceles set
in ℝ^d has size at most (d+2)(d+1)/2.
-/
theorem erdos_problem_503 (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : IsIsoscelesSet A) :
    A.card ≤ (d + 2) * (d + 1) / 2 :=
  sorry

end
