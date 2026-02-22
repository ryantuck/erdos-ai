import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #754

Let f(n) be maximal such that there exists a set A of n points in ℝ⁴
in which every x ∈ A has at least f(n) points in A equidistant from x.

Is it true that f(n) ≤ n/2 + O(1)?

Avis, Erdős, and Pach [AEP88] proved that n/2 + 2 ≤ f(n) ≤ (1 + o(1))n/2.
This was proved by Swanepoel [Sw13].

Tags: geometry | distances
-/

open Classical

noncomputable section

/--
**Erdős Problem #754** [Er94b]:

Let f(n) be the largest k such that there exists a set A of n points in ℝ⁴
where every x ∈ A has at least k other points in A all at the same distance
from x. Is it true that f(n) ≤ n/2 + O(1)?

Formulated as: there exists a constant C such that for every finite set
A ⊆ ℝ⁴ of n points, if every point x ∈ A has at least k other points at
a common distance from x, then k ≤ n/2 + C.
-/
theorem erdos_problem_754 :
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 4)),
      A.card = n →
      ∀ k : ℕ,
        (∀ x ∈ A, ∃ d : ℝ,
          k ≤ (A.filter (fun y => x ≠ y ∧ dist x y = d)).card) →
        (k : ℝ) ≤ n / 2 + C :=
  sorry

end
