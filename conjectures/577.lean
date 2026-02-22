import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card

open SimpleGraph

/-!
# Erdős Problem #577

If G is a graph with 4k vertices and minimum degree at least 2k then G
contains k vertex-disjoint 4-cycles.

A conjecture of Erdős and Faudree [Er90c]. Proved by Wang [Wa10].
-/

/-- Four vertices form a 4-cycle in G: they are pairwise distinct and
    adjacent in cyclic order a ~ b ~ c ~ d ~ a. -/
def IsFourCycle577 {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The set of vertices in a 4-tuple. -/
def fourCycleVertices577 {V : Type*} (t : V × V × V × V) : Set V :=
  let (a, b, c, d) := t; {a, b, c, d}

/--
Erdős Problem #577 [Er90c]:

If G is a graph with 4k vertices and minimum degree at least 2k then G
contains k vertex-disjoint 4-cycles.

A conjecture of Erdős and Faudree. Proved by Wang [Wa10].
-/
theorem erdos_problem_577 :
    ∀ (k : ℕ)
      (G : SimpleGraph (Fin (4 * k))) (dG : DecidableRel G.Adj),
      haveI := dG;
      (∀ v : Fin (4 * k), 2 * k ≤ G.degree v) →
      ∃ cycles : Fin k → Fin (4 * k) × Fin (4 * k) × Fin (4 * k) × Fin (4 * k),
        (∀ i, let (a, b, c, d) := cycles i; IsFourCycle577 G a b c d) ∧
        (∀ i j, i ≠ j →
          Disjoint (fourCycleVertices577 (cycles i)) (fourCycleVertices577 (cycles j))) :=
  sorry
