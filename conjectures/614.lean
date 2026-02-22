import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice

open Classical SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #614

Let $f(n,k)$ be minimal such that there is a graph with $n$ vertices and $f(n,k)$ edges
where every set of $k+2$ vertices induces a subgraph with maximum degree at least $k$.
Determine $f(n,k)$.

A problem of Erdős, Faudree, Rousseau, and Schelp [FRS97].

Tags: graph theory
-/

/-- A graph `G` on `Fin n` has the **(n,k)-induced degree property** if every subset of
    exactly `k + 2` vertices contains a vertex adjacent to at least `k` other vertices
    in the subset (i.e., the induced subgraph on that subset has maximum degree ≥ k). -/
def HasInducedDegreeProp {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k + 2 →
    ∃ v ∈ S, k ≤ (S.filter (G.Adj v)).card

/-- `erdos614_f n k` is the minimum number of edges in a graph on `n` vertices such that
    every subset of `k + 2` vertices induces a subgraph with maximum degree at least `k`.
    This is the function `f(n, k)` from Erdős Problem #614. -/
noncomputable def erdos614_f (n k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.edgeFinset.card = m ∧ HasInducedDegreeProp G k}

/--
**Erdős Problem #614** [FRS97]:

For `n ≥ k + 2`, the function `f(n, k)` is well-defined. The complete graph on `n` vertices
witnesses this: every (k+2)-element induced subgraph is K_{k+2} with maximum degree k+1 ≥ k.
The problem asks to determine the exact value of `f(n, k)`.
-/
theorem erdos_problem_614 (n k : ℕ) (hn : n ≥ k + 2) :
    ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card = erdos614_f n k ∧ HasInducedDegreeProp G k :=
  sorry

end
