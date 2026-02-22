import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Girth

open SimpleGraph

/-!
# Erdős Problem #1006

Let G be a graph with girth > 4 (that is, it contains no cycles of length 3 or 4).
Can the edges of G always be directed such that there is no directed cycle, and
reversing the direction of any edge also creates no directed cycle?

This was disproved by Nešetřil and Rödl [NeRo78b], who proved that for every
integer g, there is a graph G with girth g such that every orientation of G either
contains a directed cycle or contains a cycle obtained by reversing one edge.
-/

variable {V : Type*}

/-- An orientation of a simple graph G: a relation `dir` on V such that for each
    edge {u, v}, exactly one of `dir u v` or `dir v u` holds, and `dir` only
    relates adjacent vertices. -/
structure Orientation (G : SimpleGraph V) where
  dir : V → V → Prop
  adj_of_dir : ∀ u v, dir u v → G.Adj u v
  dir_of_adj : ∀ u v, G.Adj u v → dir u v ∨ dir v u
  antisymm : ∀ u v, dir u v → ¬dir v u

/-- An orientation is acyclic if the transitive closure of its direction relation
    is irreflexive (equivalently, there are no directed cycles). -/
def Orientation.IsAcyclic {G : SimpleGraph V} (o : Orientation G) : Prop :=
  ∀ v, ¬Relation.TransGen o.dir v v

/-- The relation obtained by flipping one directed edge (a → b) to (b → a),
    keeping all other directed edges the same. -/
def flipDir (dir : V → V → Prop) (a b : V) : V → V → Prop :=
  fun u v => (u = b ∧ v = a ∧ dir a b) ∨ (dir u v ∧ ¬(u = a ∧ v = b))

/-- An orientation is robustly acyclic if it is acyclic and reversing any
    single directed edge also yields an acyclic relation. -/
def Orientation.IsRobustlyAcyclic {G : SimpleGraph V} (o : Orientation G) : Prop :=
  o.IsAcyclic ∧
  ∀ a b, o.dir a b →
    ∀ v, ¬Relation.TransGen (flipDir o.dir a b) v v

/--
Erdős Problem #1006 (disproved) [Er71][Er76b]:

For every graph G with girth > 4, there exists an orientation of G that is
robustly acyclic (acyclic, and remains acyclic after reversing any single edge).

This was disproved by Nešetřil and Rödl [NeRo78b].
-/
theorem erdos_problem_1006 (V : Type*) (G : SimpleGraph V)
    (hgirth : 5 ≤ G.egirth) :
    ∃ o : Orientation G, o.IsRobustlyAcyclic :=
  sorry
