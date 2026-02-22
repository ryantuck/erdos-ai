import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

/-!
# Erdős Problem #616

Let r ≥ 3. For an r-uniform hypergraph G let τ(G) denote the covering number
(or transversal number), the minimum size of a set of vertices which includes
at least one from each edge in G.

Determine the best possible t such that, if G is an r-uniform hypergraph
where every subgraph G' on at most 3r - 3 vertices has τ(G') ≤ 1, we have
τ(G) ≤ t.

Erdős, Hajnal, and Tuza [EHT91] proved that (3/16)r + 7/8 ≤ t ≤ (1/5)r.
-/

/-- An r-uniform hypergraph on vertex set `Fin n`. -/
structure UniformHypergraph (n r : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- A set S of vertices is a transversal of hypergraph G if it meets every edge. -/
def IsTransversal {n r : ℕ} (G : UniformHypergraph n r) (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ G.edges, ∃ v ∈ S, v ∈ e

/-- The covering number τ(G): the minimum size of a transversal. -/
noncomputable def coveringNumber {n r : ℕ} (G : UniformHypergraph n r) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Fin n), S.card = k ∧ IsTransversal G S}

/-- The subhypergraph of G induced on vertex set W: edges of G contained in W. -/
def inducedSub {n r : ℕ} (G : UniformHypergraph n r) (W : Finset (Fin n)) :
    UniformHypergraph n r where
  edges := G.edges.filter (· ⊆ W)
  uniform := fun e he => G.uniform e (Finset.mem_filter.mp he).1

/-- The local covering property: every induced subhypergraph on at most
    3r - 3 vertices has covering number at most 1. -/
def HasLocalCoveringProperty {n r : ℕ} (G : UniformHypergraph n r) : Prop :=
  ∀ W : Finset (Fin n), W.card ≤ 3 * r - 3 → coveringNumber (inducedSub G W) ≤ 1

/--
Erdős Problem #616 — Upper bound (Erdős–Hajnal–Tuza [EHT91]):
If G is an r-uniform hypergraph (r ≥ 3) where every subhypergraph on at most
3r - 3 vertices has covering number ≤ 1, then τ(G) ≤ (1/5)r.
-/
theorem erdos_problem_616_upper_bound :
    ∀ r : ℕ, 3 ≤ r →
    ∀ n : ℕ, ∀ G : UniformHypergraph n r,
    HasLocalCoveringProperty G →
    (coveringNumber G : ℝ) ≤ (1 : ℝ) / 5 * (r : ℝ) :=
  sorry

/--
Erdős Problem #616 — Lower bound (Erdős–Hajnal–Tuza [EHT91]):
For every r ≥ 3, there exists an r-uniform hypergraph G satisfying the local
covering property with τ(G) ≥ (3/16)r + 7/8.
-/
theorem erdos_problem_616_lower_bound :
    ∀ r : ℕ, 3 ≤ r →
    ∃ n : ℕ, ∃ G : UniformHypergraph n r,
    HasLocalCoveringProperty G ∧
    (coveringNumber G : ℝ) ≥ (3 : ℝ) / 16 * (r : ℝ) + 7 / 8 :=
  sorry
