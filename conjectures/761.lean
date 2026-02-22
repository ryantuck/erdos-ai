import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #761

The cochromatic number of G, denoted by ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either
a complete graph or empty graph. The dichromatic number of G, denoted by δ(G),
is the minimum number k of colours required such that, in any orientation of
the edges of G, there is a k-colouring of the vertices of G such that there
are no monochromatic oriented cycles.

Must a graph with large chromatic number have large dichromatic number?
Must a graph with large cochromatic number contain a graph with large
dichromatic number?

The first question is due to Erdős and Neumann-Lara. The second question is
due to Erdős and Gimbel. A positive answer to the second question implies a
positive answer to the first via the bound mentioned in [760].

Tags: graph theory, chromatic number
-/

/-- An orientation of a simple graph assigns a direction to each edge:
    each edge {u,v} is oriented as u→v or v→u (but not both). -/
def IsOrientation761 {V : Type*} (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → D u v ∨ D v u) ∧
  (∀ u v, D u v → ¬D v u)

/-- A colouring c : V → Fin k is acyclic with respect to an orientation D if
    there is no monochromatic directed cycle: no vertex can reach itself
    via directed edges within its own colour class. -/
def IsAcyclicColouring761 {V : Type*} (D : V → V → Prop) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k, ∀ v : V, c v = i →
    ¬Relation.TransGen (fun u w => c u = i ∧ c w = i ∧ D u w) v v

/-- The dichromatic number of G: the minimum k such that for every orientation
    of G, there exists an acyclic k-colouring. -/
noncomputable def dichromaticNumber761 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ D : V → V → Prop, IsOrientation761 G D →
    ∃ c : V → Fin k, IsAcyclicColouring761 D k c}

/-- A cochromatic colouring: each colour class induces either a complete
    subgraph or an independent set. -/
def IsCochromaticColouring761 {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): minimum number of colours in a cochromatic
    colouring. -/
noncomputable def cochromaticNumber761 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring761 G k c}

/--
**Erdős Problem #761, Question 1** (Erdős–Neumann-Lara):

Must a graph with large chromatic number have large dichromatic number?
For every n there exists m such that χ(G) ≥ m implies δ(G) ≥ n.
-/
theorem erdos_problem_761a :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (s : ℕ) (G : SimpleGraph (Fin s)),
      G.chromaticNumber.toNat ≥ m →
        dichromaticNumber761 G ≥ n :=
  sorry

/--
**Erdős Problem #761, Question 2** (Erdős–Gimbel):

Must a graph with large cochromatic number contain a subgraph with large
dichromatic number? For every n there exists m such that ζ(G) ≥ m implies
G contains an induced subgraph with δ ≥ n.
-/
theorem erdos_problem_761b :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (s : ℕ) (G : SimpleGraph (Fin s)),
      cochromaticNumber761 G ≥ m →
        ∃ (S : Finset (Fin s)),
          dichromaticNumber761 (G.induce (↑S : Set (Fin s))) ≥ n :=
  sorry

end
