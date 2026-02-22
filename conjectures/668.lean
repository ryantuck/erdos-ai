import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #668

Is it true that the number of incongruent sets of n points in ℝ² which
maximise the number of unit distances tends to infinity as n → ∞?
Is it always > 1 for n > 3?

In fact this is = 1 also for n = 4, the unique example given by two
equilateral triangles joined by an edge.

The actual maximal number of unit distances is the subject of problem #90.

A problem of Erdős [Er97f].

Tags: geometry | distances
-/

open Classical

noncomputable section

/-- The number of ordered pairs of distinct points in P at unit distance. -/
noncomputable def unitDistanceCount668
    (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1)).card

/-- The maximum number of ordered unit distance pairs among all n-point
    sets in ℝ². -/
noncomputable def maxUnitDistances668 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ unitDistanceCount668 P = k}

/-- Two finite point sets in ℝ² are congruent if there is a distance-preserving
    map of ℝ² sending one onto the other. -/
def AreCongruent668
    (P Q : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    (∀ x y, dist (f x) (f y) = dist x y) ∧
    f '' (↑P : Set (EuclideanSpace ℝ (Fin 2))) = ↑Q

/--
**Erdős Problem #668, Part 1** [Er97f]:

The number of incongruent n-point sets in ℝ² maximising the number of unit
distances tends to infinity as n → ∞.

Formulated as: for every M, there exists N such that for all n ≥ N, there
exist M pairwise non-congruent n-point sets each achieving the maximum
unit distance count.
-/
theorem erdos_problem_668_part1 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (Ps : Fin M → Finset (EuclideanSpace ℝ (Fin 2))),
        (∀ i, (Ps i).card = n ∧
              unitDistanceCount668 (Ps i) = maxUnitDistances668 n) ∧
        (∀ i j, i ≠ j → ¬AreCongruent668 (Ps i) (Ps j)) :=
  sorry

/--
**Erdős Problem #668, Part 2** [Er97f]:

For every n > 3, there exist at least two incongruent n-point sets in ℝ²
achieving the maximum number of unit distances.

Note: the additional commentary on the problem states that the count of
incongruent maximisers is in fact = 1 for n = 4, so this part of the
conjecture may be false as stated.
-/
theorem erdos_problem_668_part2 (n : ℕ) (hn : n > 3) :
    ∃ (P Q : Finset (EuclideanSpace ℝ (Fin 2))),
      P.card = n ∧ Q.card = n ∧
      unitDistanceCount668 P = maxUnitDistances668 n ∧
      unitDistanceCount668 Q = maxUnitDistances668 n ∧
      ¬AreCongruent668 P Q :=
  sorry

end
