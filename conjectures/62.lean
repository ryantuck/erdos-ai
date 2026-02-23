import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open SimpleGraph Cardinal

/-- A graph G has chromatic number ℵ₁ if it cannot be properly colored by any
    countable set of colors, but can be colored by a set of cardinality ℵ₁. -/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/-- G contains H as a subgraph via an injective adjacency-preserving map. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #62 (weak version):

If G₁, G₂ are two graphs with chromatic number ℵ₁, must there exist a graph H
with chromatic number at least 4 which is a subgraph of both G₁ and G₂?

Every graph with chromatic number ℵ₁ contains all sufficiently large odd
cycles (chromatic number 3), proved by Erdős, Hajnal, and Shelah [EHS74].
Erdős wrote [Er87] that 'probably' every graph with chromatic number ℵ₁
contains as subgraphs all graphs with chromatic number 4 with sufficiently
large girth.
-/
theorem erdos_problem_62_weak :
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticNumberAleph1 G₁ →
    HasChromaticNumberAleph1 G₂ →
    ∃ (U : Type*) (H : SimpleGraph U),
      ¬ H.Colorable 3 ∧
      containsSubgraph G₁ H ∧
      containsSubgraph G₂ H :=
  sorry

/--
Erdős Problem #62 (strong version):

If G₁, G₂ are two graphs with chromatic number ℵ₁, must there exist a graph H
with infinite chromatic number (χ ≥ ℵ₀) which is a subgraph of both G₁ and G₂?

This is the stronger form of the conjecture. Erdős also asked [Er87] about
finding such a common subgraph in any finite collection of graphs with
chromatic number ℵ₁.
-/
theorem erdos_problem_62 :
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticNumberAleph1 G₁ →
    HasChromaticNumberAleph1 G₂ →
    ∃ (U : Type*) (H : SimpleGraph U),
      H.chromaticNumber = ⊤ ∧
      containsSubgraph G₁ H ∧
      containsSubgraph G₂ H :=
  sorry
