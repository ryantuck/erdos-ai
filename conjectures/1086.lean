import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

/-!
# Erdős Problem #1086

Let g(n) be minimal such that any set of n points in ℝ² contains the vertices
of at most g(n) many triangles with the same area. Estimate g(n).

Equivalently, how many triangles of area 1 can a set of n points in ℝ²
determine? This question is attributed to Oppenheim.

Erdős and Purdy [ErPu71] proved:
  n² log log n ≪ g(n) ≪ n^{5/2}
and believed the lower bound to be closer to the truth.

The best known upper bound is g(n) ≪ n^{20/9} by Raz and Sharir [RaSh17].

The conjecture is that g(n) = O(n^{2+ε}) for every ε > 0.
-/

noncomputable section

/-- The area of a triangle in ℝ² with vertices p, q, r, computed as
half the absolute value of the cross product (q - p) × (r - p). -/
def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)| / 2

/-- The number of ordered triples of distinct points from S ⊆ ℝ² that form
a triangle with area exactly A. Each unordered triangle is counted 6 times
(once per ordering of its vertices). -/
noncomputable def countTrianglesWithArea (S : Finset (ℝ × ℝ)) (A : ℝ) : ℕ :=
  ((S ×ˢ (S ×ˢ S)).filter (fun (p, q, r) =>
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r = A)).card

/--
Erdős Problem #1086 (Erdős-Purdy conjecture on equal-area triangles):

For every ε > 0, there exists C > 0 such that for every finite set S of
points in ℝ² and every area A, the number of triangles with area A
determined by S is at most C · |S|^{2+ε}.

This formalizes the belief of Erdős and Purdy that g(n) ≪ n^{2+ε},
where g(n) is the maximum number of triangles of the same area in any
set of n points. The statement uses ordered triples, so the constant C
absorbs the factor of 6.
-/
theorem erdos_problem_1086 :
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (ℝ × ℝ)) (A : ℝ),
      (countTrianglesWithArea S A : ℝ) ≤ C * (S.card : ℝ) ^ (2 + ε) :=
  sorry

end
