import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Classical SimpleGraph Finset

/-!
# Erdős Problem #805

For which functions g(n) with n > g(n) ≥ (log n)² is there a graph on n vertices
in which every induced subgraph on g(n) vertices contains a clique of size ≥ log n
and an independent set of size ≥ log n?

In particular, is there such a graph for g(n) = (log n)³?

A problem of Erdős and Hajnal [Er91], who thought there is no such graph for
g(n) = (log n)³.

Alon and Sudakov [AlSu07] proved there is no such graph with
g(n) = c · (log n)³ / log(log n) for some constant c > 0.

Alon, Bucić, and Sudakov [ABS21] construct such a graph with
g(n) ≤ 2^{2^{(log log n)^{1/2 + o(1)}}}.
-/

/-- A clique in a simple graph: a finset of vertices where every two distinct
    members are adjacent. -/
def SimpleGraph.IsFinsetClique {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- An independent set in a simple graph: a finset of vertices with no edges
    between any two of its members. -/
def SimpleGraph.IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

/-- The Erdős-Hajnal property for Problem 805: a graph G on Fin n has the property
    that every induced subgraph on m vertices contains both a clique and an
    independent set of size at least k. -/
def erdos805_property {n : ℕ} (G : SimpleGraph (Fin n)) (m k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m →
    (∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ k ∧ G.IsFinsetClique T) ∧
    (∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ k ∧ G.IsIndepSet T)

/--
Erdős-Hajnal conjecture [Er91]: there is no graph on n vertices such that every
induced subgraph on ⌊(log n)³⌋ vertices contains both a clique and an independent
set of size ≥ ⌈log n⌉.
-/
theorem erdos_805_conjecture :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ¬∃ G : SimpleGraph (Fin n), erdos805_property G
        (Nat.floor ((Real.log (n : ℝ)) ^ 3))
        (Nat.ceil (Real.log (n : ℝ))) :=
  sorry

/--
Alon-Sudakov [AlSu07]: there is no such graph with
g(n) = c · (log n)³ / log(log n) for some constant c > 0.
This strengthens the Erdős-Hajnal conjecture.
-/
theorem erdos_805_alon_sudakov :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ¬∃ G : SimpleGraph (Fin n), erdos805_property G
        (Nat.floor (c * (Real.log (n : ℝ)) ^ 3 / Real.log (Real.log (n : ℝ))))
        (Nat.ceil (Real.log (n : ℝ))) :=
  sorry

/--
Alon-Bucić-Sudakov [ABS21]: for every ε > 0, for sufficiently large n,
there exists a graph on n vertices satisfying the property with
g(n) = ⌊2^{2^{(log log n)^{1/2+ε}}}⌋.
-/
theorem erdos_805_alon_bucic_sudakov :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ G : SimpleGraph (Fin n), erdos805_property G
          (Nat.floor ((2 : ℝ) ^ ((2 : ℝ) ^ ((Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2 + ε)))))
          (Nat.ceil (Real.log (n : ℝ))) :=
  sorry

end
