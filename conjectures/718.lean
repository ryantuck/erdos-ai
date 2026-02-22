import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #718

Is there some constant C > 0 such that any graph on n vertices with ≥ Cr²n edges
contains a subdivision of K_r?

A conjecture of Erdős, Hajnal, and Mader. Dirac proved that every graph on n vertices
with at least 2n-2 edges contains a subdivision of K_4, and conjectured that 3n-5 edges
forces a subdivision of K_5.

Mader proved that ≥ 2^(r choose 2) · n edges suffices.

The answer is yes, proved independently by Komlós and Szemerédi [KoSz96] and Bollobás
and Thomason [BoTh96].

Tags: graph theory
-/

/-- A graph G contains a subdivision of K_k if there exist k distinct branch vertices
    and internally vertex-disjoint paths between every pair of branch vertices. -/
def SimpleGraph.ContainsSubdivision {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k ↪ V)
    (paths : ∀ (i j : Fin k), i < j → G.Walk (f i) (f j)),
    (∀ i j (h : i < j), (paths i j h).IsPath) ∧
    (∀ i₁ j₁ (h₁ : i₁ < j₁) i₂ j₂ (h₂ : i₂ < j₂),
      (i₁, j₁) ≠ (i₂, j₂) →
      ∀ v, v ∈ (paths i₁ j₁ h₁).support.tail.dropLast →
           v ∉ (paths i₂ j₂ h₂).support.tail.dropLast) ∧
    (∀ i j (h : i < j) v,
      v ∈ (paths i j h).support.tail.dropLast →
      ∀ m : Fin k, v ≠ f m)

/--
**Erdős Problem #718** (PROVED, Komlós–Szemerédi [KoSz96], Bollobás–Thomason [BoTh96]):

There exists an absolute constant C > 0 such that any graph on n vertices
with at least C · r² · n edges contains a subdivision of K_r.
-/
theorem erdos_problem_718 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n r : ℕ),
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (G.edgeFinset.card : ℝ) ≥ C * (r : ℝ) ^ 2 * (n : ℝ) →
          G.ContainsSubdivision r := by
  sorry
