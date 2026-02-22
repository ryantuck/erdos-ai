import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

open Finset

/-!
# Erdős Problem #834

Does there exist a 3-critical 3-uniform hypergraph in which every vertex
has degree ≥ 7?

A problem of Erdős and Lovász [Er74d].

There are two natural interpretations of "3-critical":

1. **Transversal criticality**: the minimum transversal (hitting set) has
   size 3, and for every edge e the hypergraph H \ {e} has a transversal
   of size ≤ 2.

2. **Chromatic criticality**: the chromatic number is 3, but deleting any
   edge or vertex reduces the chromatic number to at most 2.

Li [Li25] resolved both formulations:
- In the transversal formulation, every 3-critical 3-uniform hypergraph
  has a vertex of degree ≤ 6 (answer: NO).
- In the chromatic formulation, there exists a 3-critical 3-uniform
  hypergraph on 9 vertices with minimum degree 7 (answer: YES).
-/

/-- A hypergraph on vertex type V, represented as a finset of edges,
where each edge is a finset of vertices. -/
structure Hypergraph (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)

/-- A hypergraph is r-uniform if every edge has exactly r vertices. -/
def Hypergraph.IsUniform {V : Type*} [DecidableEq V] (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- The degree of a vertex v in a hypergraph is the number of edges containing v. -/
def Hypergraph.degree {V : Type*} [DecidableEq V] (H : Hypergraph V) (v : V) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

/-- The vertices of a hypergraph (the union of all edges). -/
def Hypergraph.vertices {V : Type*} [DecidableEq V] (H : Hypergraph V) : Finset V :=
  H.edges.biUnion id

/-- The hypergraph obtained by removing an edge. -/
def Hypergraph.eraseEdge {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (e : Finset V) : Hypergraph V :=
  ⟨H.edges.erase e⟩

/-- The hypergraph obtained by removing a vertex (and all edges containing it). -/
def Hypergraph.eraseVertex {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (v : V) : Hypergraph V :=
  ⟨H.edges.filter (fun e => v ∉ e)⟩

/-- A proper coloring of a hypergraph: no edge is monochromatic. -/
def Hypergraph.IsProperColoring {V : Type*} [DecidableEq V] (H : Hypergraph V)
    {α : Type*} (f : V → α) : Prop :=
  ∀ e ∈ H.edges, e.card ≥ 2 → ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- A set S is a transversal (hitting set) of H if it intersects every edge. -/
def Hypergraph.IsTransversal {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (S : Finset V) : Prop :=
  ∀ e ∈ H.edges, ∃ v ∈ e, v ∈ S

/-- A hypergraph is 3-transversal-critical if the minimum transversal has
    size 3 and removing any single edge allows a transversal of size ≤ 2. -/
def Hypergraph.Is3TransversalCritical {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : Prop :=
  (∃ S : Finset V, S.card = 3 ∧ H.IsTransversal S) ∧
  (∀ S : Finset V, S.card < 3 → ¬H.IsTransversal S) ∧
  (∀ e ∈ H.edges, ∃ S : Finset V, S.card ≤ 2 ∧ (H.eraseEdge e).IsTransversal S)

/-- A hypergraph is 3-chromatic-critical if its chromatic number is 3 and
    removing any edge or vertex makes it 2-colorable. -/
def Hypergraph.Is3ChromaticCritical {V : Type*} [DecidableEq V]
    (H : Hypergraph V) : Prop :=
  (∃ f : V → Fin 3, H.IsProperColoring f) ∧
  (∀ f : V → Fin 2, ¬H.IsProperColoring f) ∧
  (∀ e ∈ H.edges, ∃ f : V → Fin 2, (H.eraseEdge e).IsProperColoring f) ∧
  (∀ v : V, v ∈ H.vertices → ∃ f : V → Fin 2, (H.eraseVertex v).IsProperColoring f)

/--
Erdős Problem #834, transversal formulation (resolved by Li [Li25]):

Every 3-transversal-critical 3-uniform hypergraph has a vertex of degree ≤ 6.
In particular, there is no such hypergraph with minimum degree ≥ 7.
-/
theorem erdos_problem_834_transversal (n : ℕ) (H : Hypergraph (Fin n))
    (hunif : H.IsUniform 3) (hcrit : H.Is3TransversalCritical) :
    ∃ v : Fin n, H.degree v ≤ 6 :=
  sorry

/--
Erdős Problem #834, chromatic formulation (resolved by Li [Li25]):

There exists a 3-chromatic-critical 3-uniform hypergraph on 9 vertices
with minimum degree ≥ 7.
-/
theorem erdos_problem_834_chromatic :
    ∃ (H : Hypergraph (Fin 9)), H.IsUniform 3 ∧ H.Is3ChromaticCritical ∧
      ∀ v : Fin 9, H.degree v ≥ 7 :=
  sorry
