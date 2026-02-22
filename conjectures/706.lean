import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #706

Let L(r) be such that if G is a graph formed by taking a finite set of points P in ℝ²
and some set A ⊂ (0,∞) of size r, where the vertex set is P and there is an edge between
two points if and only if their distance is a member of A, then χ(G) ≤ L(r).

Estimate L(r). In particular, is it true that L(r) ≤ r^{O(1)}?

The case r = 1 is the Hadwiger-Nelson problem, for which 5 ≤ L(1) ≤ 7.

See also [508], [704], [705].

https://www.erdosproblems.com/706
-/

/-- The multi-distance graph in ℝ²: given a set A of positive reals, two points
    are adjacent iff their Euclidean distance belongs to A. -/
def multiDistanceGraph (A : Set ℝ) : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := x ≠ y ∧ dist x y ∈ A
  symm := fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/--
Erdős Problem #706:

Is it true that L(r) ≤ r^{O(1)}? That is, does there exist a polynomial bound
on the chromatic number of multi-distance graphs in ℝ² as a function of the
number of allowed distances?

Formalized as: there exist constants C, K ∈ ℕ such that for all r ≥ 1 and all
sets A of r positive real distances, the multi-distance graph on ℝ² with
distance set A is (C · r^K)-colorable.
-/
theorem erdos_problem_706 :
    ∃ C K : ℕ, ∀ (r : ℕ), 1 ≤ r → ∀ (A : Finset ℝ), A.card = r →
    (∀ a ∈ A, (0 : ℝ) < a) →
    (multiDistanceGraph (↑A : Set ℝ)).Colorable (C * r ^ K) :=
  sorry

end
