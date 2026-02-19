import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Isometry

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
minimal-diameter unit-separated n-point configurations under congruence.
-/
noncomputable def h (n : ℕ) : ℕ :=
  let minimizers : Set (Finset (EuclideanSpace ℝ (Fin 2))) :=
    {A | A.card = n ∧ IsMinimalDiameter A}
  Set.ncard {C : Set (Finset (EuclideanSpace ℝ (Fin 2))) |
    ∃ A ∈ minimizers, C = minimizers ∩ {B | AreCongruent A B}}

/--
Erdős Problem #103:
Let h(n) count the number of incongruent sets of n points in ℝ² which minimize
the diameter subject to the constraint that d(x,y) ≥ 1 for all distinct points
x, y. The conjecture is that h(n) → ∞ as n → ∞.

It is not even known whether h(n) ≥ 2 for all sufficiently large n.
-/
theorem erdos_problem_103 : ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → h n ≥ M :=
  sorry
