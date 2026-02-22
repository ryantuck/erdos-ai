import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Card

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #715

Does every regular graph of degree 4 contain a regular subgraph of degree 3?
Is there any r such that every regular graph of degree r must contain a regular
subgraph of degree 3?

A problem of Berge (or Berge and Sauer). Alon, Friedland, and Kalai [AFK84]
proved that every 4-regular graph plus an edge contains a 3-regular subgraph,
and hence in particular every r-regular graph with r ≥ 5 contains a 3-regular
subgraph.

The answer is yes, proved by Tashkinov [Ta82].

Tags: graph theory
-/

/--
**Erdős Problem #715, Part 1** (PROVED) [Er75][Er81]:

Every 4-regular simple graph contains a 3-regular subgraph.

A subgraph H of G is 3-regular if every vertex of H has exactly 3 neighbours
in H. We express this using Mathlib's `SimpleGraph.Subgraph`: there exists a
subgraph H of G such that H.coe (the coercion to a SimpleGraph on H.verts)
is 3-regular, and H has at least one vertex.

Proved by Tashkinov [Ta82].
-/
theorem erdos_problem_715a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 4) :
    ∃ H : G.Subgraph,
      H.verts.Nonempty ∧
      ∀ v : H.verts, H.degree v = 3 :=
  sorry

/--
**Erdős Problem #715, Part 2** (PROVED) [AFK84]:

Every r-regular simple graph with r ≥ 5 contains a 3-regular subgraph.

Proved by Alon, Friedland, and Kalai [AFK84].
-/
theorem erdos_problem_715b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : r ≥ 5)
    (hreg : G.IsRegularOfDegree r) :
    ∃ H : G.Subgraph,
      H.verts.Nonempty ∧
      ∀ v : H.verts, H.degree v = 3 :=
  sorry
