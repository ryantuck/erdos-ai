import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Data.Fintype.Basic

open TopologicalSpace Set Classical

noncomputable section

/-!
# Erdős Problem #909

Let n ≥ 2. Is there a (topological) space S of dimension n such that S × S
also has dimension n?

The space of rational points in Hilbert space has this property for n = 1.
This was proved for general n by Anderson and Keisler [AnKe67].

Tags: analysis, topology
-/

/-- A topological space has covering dimension at most n if every finite open
    cover has a finite open refinement of order at most n + 1, meaning every
    point belongs to at most n + 1 sets of the refinement. -/
def coveringDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (U : ι → Set X),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    ∃ (κ : Type) (_ : Fintype κ) (V : κ → Set X),
      (∀ k, IsOpen (V k)) ∧
      (⋃ k, V k) = univ ∧
      (∀ k, ∃ i, V k ⊆ U i) ∧
      ∀ x : X, (Finset.univ.filter (fun k => x ∈ V k)).card ≤ n + 1

/-- A topological space has covering dimension exactly n. -/
def hasCoveringDim (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  coveringDimLE X n ∧ ∀ m : ℕ, m < n → ¬coveringDimLE X m

/--
Erdős Problem #909 (proved by Anderson and Keisler [AnKe67]):

For every n ≥ 2, there exists a topological space S of covering dimension n
such that S × S also has covering dimension n.
-/
theorem erdos_problem_909 (n : ℕ) (hn : n ≥ 2) :
    ∃ (S : Type) (_ : TopologicalSpace S),
      hasCoveringDim S n ∧ hasCoveringDim (S × S) n :=
  sorry

end
