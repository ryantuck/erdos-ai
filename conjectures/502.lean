import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Choose.Basic

noncomputable section

/--
A finite set of points in ℝ^n is a two-distance set if there are exactly
two distinct positive real numbers that occur as distances between pairs
of distinct points.
-/
def IsTwoDistanceSet {n : ℕ} (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  Set.ncard {d : ℝ | ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ d = dist x y} = 2

/--
Erdős Problem #502 — Bannai–Bannai–Stanton Upper Bound [Er61] [BBS83]:

What is the size of the largest A ⊆ ℝ^n such that there are only two
distinct distances between elements of A?

Originally asked to Erdős by Coxeter. Bannai, Bannai, and Stanton proved
that |A| ≤ C(n+2, 2). A simpler proof was given by Petrov and Pohoata
[PePo21]. The best known lower bound is C(n+1, 2) via a construction
of Alweiss.
-/
theorem erdos_problem_502
    (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n)))
    (hA : IsTwoDistanceSet A) :
    A.card ≤ Nat.choose (n + 2) 2 :=
  sorry

end
