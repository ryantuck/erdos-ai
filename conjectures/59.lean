import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-- An injective graph homomorphism from H to G; witnesses that G contains a
    subgraph isomorphic to H. -/
def containsSubgraph59 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber59 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph59 F H ∧ F.edgeFinset.card = m}

/-- The number of labeled simple graphs on n vertices that do not contain H as a subgraph. -/
noncomputable def countGFreeGraphs59 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  Nat.card {F : SimpleGraph (Fin n) // ¬containsSubgraph59 F H}

/--
Erdős Problem #59 [Er90, Er93, Er97c, Va99]:

Is it true that, for every graph G, the number of labeled graphs on n vertices that
contain no copy of G is at most 2^{(1+o(1))·ex(n;G)}?

That is, for every ε > 0, for all sufficiently large n:
  #{G-free graphs on [n]} ≤ 2^{(1+ε)·ex(n;G)}

This was DISPROVED: the answer is no for G = C₆ (the 6-cycle).
Erdős, Frankl, and Rödl [EFR86] proved the answer is yes when G is not bipartite.
Morris and Saxton [MoSa16] showed there are at least 2^{(1+c)·ex(n;C₆)} such graphs
for infinitely many n, for some constant c > 0.
-/
theorem erdos_problem_59 :
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countGFreeGraphs59 H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (turanNumber59 H n : ℝ)) :=
  sorry
