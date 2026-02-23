import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-- A simple graph contains a 4-cycle (C₄) if there exist four distinct vertices
    a, b, c, d forming the cycle a-b-c-d-a. -/
def ContainsCycleFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A simple graph is C₄-free if it contains no 4-cycle as a subgraph. -/
def CycleFourFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ContainsCycleFour G

/--
Erdős Problem #1008 (Proved by Conlon, Fox, and Sudakov [CFS14b]):
There exists an absolute constant c > 0 such that every graph with m edges
contains a C₄-free subgraph with at least c · m^{2/3} edges.

Originally asked by Bollobás and Erdős with m^{3/4} in place of m^{2/3},
but Folkman showed the m^{3/4} version is false. Erdős [Er71] revised the
conjecture to m^{2/3}, noting ≫ m^{1/2} is trivial.
-/
theorem erdos_problem_1008 :
    ∃ c : ℝ, c > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ∃ H : SimpleGraph (Fin n),
          H ≤ G ∧
          CycleFourFree H ∧
          c * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) ≤ (H.edgeFinset.card : ℝ) :=
  sorry

end
