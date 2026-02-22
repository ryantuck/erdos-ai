import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-- An injective graph homomorphism from H to G; witnesses that G contains a
    subgraph isomorphic to H. -/
def containsSubgraph926 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber926 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph926 F H ∧ F.edgeFinset.card = m}

/-- Vertex type for the graph H_k: one center vertex x, k spoke vertices y₁,...,yₖ,
    and one pair vertex z_{ij} for each pair (i,j) with i < j ≤ k. -/
abbrev HkVertex926 (k : ℕ) := Unit ⊕ Fin k ⊕ { p : Fin k × Fin k // p.1 < p.2 }

/-- The graph H_k from Erdős Problem #926.
    The center vertex x is adjacent to all spoke vertices yᵢ,
    and each pair vertex z_{ij} (for i < j) is adjacent to yᵢ and yⱼ. -/
def erdosGraphHk (k : ℕ) : SimpleGraph (HkVertex926 k) where
  Adj := fun v w => match v, w with
    | Sum.inl (), Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inl () => True
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr ⟨(a, b), _⟩) => i = a ∨ i = b
    | Sum.inr (Sum.inr ⟨(a, b), _⟩), Sum.inr (Sum.inl i) => i = a ∨ i = b
    | _, _ => False
  symm := sorry
  loopless := sorry

/--
Erdős Problem #926 [Er69b, Er71, Er74c, Er93]:

Let k ≥ 4. Is it true that ex(n; H_k) ≪_k n^{3/2}, where H_k is the graph on
vertices x, y₁,...,yₖ, z₁,...,z_{k choose 2}, where x is adjacent to all yᵢ
and each pair yᵢ, yⱼ is adjacent to a unique z_{ij}?

The answer is yes, proved by Füredi [Fu91] who showed ex(n; H_k) ≪ (kn)^{3/2},
improved to ex(n; H_k) ≪ k · n^{3/2} by Alon, Krivelevich, and Sudakov [AKS03].
-/
theorem erdos_problem_926 :
    ∀ (k : ℕ), 4 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (turanNumber926 (erdosGraphHk k) n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry
