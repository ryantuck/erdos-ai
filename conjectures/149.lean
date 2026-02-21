import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph

/-!
# Erdős Problem #149

Let G be a graph with maximum degree Δ. Is G the union of at most (5/4)Δ²
sets of strongly independent edges (sets such that the induced subgraph is
the union of vertex-disjoint edges)?

This is equivalent to asking whether the chromatic number of the square of the
line graph L(G)² is at most (5/4)Δ².  The bound is sharp, witnessed by blowups
of C₅.  The minimum number of strongly independent edge sets needed to decompose
the edges of G is called the strong chromatic index of G.
-/

/-- A set S of edges of G is strongly independent if for any two distinct edges
    e₁, e₂ ∈ S, every endpoint u of e₁ and every endpoint v of e₂ satisfy
    u ≠ v and ¬G.Adj u v.  Equivalently, S is an independent set in L(G)²
    (the square of the line graph of G). -/
def IsStronglyIndepEdgeSet {V : Type*} (G : SimpleGraph V)
    (S : Set (Sym2 V)) : Prop :=
  S ⊆ G.edgeSet ∧
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
    ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬G.Adj u v

/-- The strong chromatic index χ'_s(G): the minimum number of strongly
    independent edge sets needed to partition the edges of G. Equivalently,
    this is the chromatic number of L(G)², the square of the line graph. -/
noncomputable def strongChromaticIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (c : G.edgeSet → Fin k),
    ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v}

/-- Erdős–Nešetřil Strong Edge Coloring Conjecture (Erdős Problem #149) [Er88]:
    For any finite graph G with maximum degree Δ,
      χ'_s(G) ≤ (5/4) · Δ²,
    i.e. the edge set of G can be partitioned into at most (5/4)Δ² strongly
    independent edge sets.  This bound is sharp: a blowup of C₅ with Δ = 2k
    requires exactly 5k² = (5/4)Δ² strong colors. -/
theorem erdos_problem_149 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (strongChromaticIndex G : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 :=
  sorry
