import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry

/--
The integer lattice ℤ² ⊆ ℝ²: points whose coordinates are all integers.
-/
def IntLattice : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i : Fin 2, ∃ n : ℤ, p i = ↑n}

/--
Erdős Problem #215 (Steinhaus Problem):
Does there exist S ⊆ ℝ² such that every set congruent to S
(that is, S after some isometry) contains exactly one point from ℤ²?

The answer is yes, proved by Jackson and Mauldin [JaMa02].
Their construction depends on the axiom of choice.
-/
theorem erdos_problem_215 :
  ∃ (S : Set (EuclideanSpace ℝ (Fin 2))),
    ∀ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      Isometry f →
      ∃! p, p ∈ f '' S ∧ p ∈ IntLattice :=
sorry
