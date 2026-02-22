import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #717

Let G be a graph on n vertices with chromatic number χ(G) and let σ(G) be
the maximal k such that G contains a subdivision of K_k. Is it true that
  χ(G) ≪ (n^{1/2} / log n) · σ(G)?

Hajós originally conjectured that χ(G) ≤ σ(G), which was proved by Dirac
when χ(G) = 4. Catlin disproved Hajós' conjecture for all χ(G) ≥ 7, and
Erdős and Fajtlowicz disproved it in a strong form, showing that for almost
all graphs on n vertices, χ(G) ≫ (n^{1/2} / log n) · σ(G).

The answer is yes, proved by Fox, Lee, and Sudakov [FLS13].

Tags: graph theory
-/

/-- A graph G contains a subdivision of K_k (a topological K_k minor) if there
    exist k distinct branch vertices and internally vertex-disjoint paths in G
    between every pair of branch vertices. -/
def SimpleGraph.ContainsSubdivision {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k ↪ V)
    (paths : ∀ (i j : Fin k), i < j → G.Walk (f i) (f j)),
    -- Each walk is a path (no repeated vertices)
    (∀ i j (h : i < j), (paths i j h).IsPath) ∧
    -- Internal vertices of different paths are disjoint
    (∀ i₁ j₁ (h₁ : i₁ < j₁) i₂ j₂ (h₂ : i₂ < j₂),
      (i₁, j₁) ≠ (i₂, j₂) →
      ∀ v, v ∈ (paths i₁ j₁ h₁).support.tail.dropLast →
           v ∉ (paths i₂ j₂ h₂).support.tail.dropLast) ∧
    -- Internal vertices are disjoint from branch vertices
    (∀ i j (h : i < j) v,
      v ∈ (paths i j h).support.tail.dropLast →
      ∀ m : Fin k, v ≠ f m)

/-- σ(G) is the maximum k such that G contains a subdivision of K_k.
    For a graph on a finite vertex type, this is always finite. -/
noncomputable def SimpleGraph.subdivisionNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | G.ContainsSubdivision k}

/--
**Erdős Problem #717** (PROVED, Fox–Lee–Sudakov [FLS13]):

For every graph G on n vertices,
  χ(G) ≤ C · √n / log(n) · σ(G)
for some absolute constant C > 0.
-/
theorem erdos_problem_717 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ), 2 ≤ n →
        ∀ (G : SimpleGraph (Fin n)),
          (G.chromaticNumber.toNat : ℝ) ≤
            C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) *
              (G.subdivisionNumber : ℝ) := by
  sorry
