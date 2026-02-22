import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #619

For a triangle-free graph $G$ let $h_r(G)$ be the smallest number of edges that
need to be added to $G$ so that it has diameter $r$ (while preserving the property
of being triangle-free).

Is it true that there exists a constant $c > 0$ such that if $G$ is a connected
graph on $n$ vertices then $h_4(G) < (1 - c)n$?

A problem of Erdős, Gyárfás, and Ruszinkó [EGR98] who proved that $h_3(G) \leq n$
and $h_5(G) \leq (n-1)/2$ and there exist connected graphs $G$ on $n$ vertices with
$h_3(G) \geq n - c$ for some constant $c > 0$.

Tags: graph theory
-/

/-- `triangleFreeDiamCompletion r G` is the minimum number of edges that must be added
    to a triangle-free graph `G` on `Fin n` so that the resulting supergraph has
    diameter at most `r` and remains triangle-free. Returns 0 if no such completion
    exists (the set is empty and sInf defaults to 0). -/
noncomputable def triangleFreeDiamCompletion {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n), G ≤ H ∧
    H.CliqueFree 3 ∧
    H.Connected ∧
    H.diam ≤ r ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

/--
**Erdős Problem #619** [EGR98][Er99]:

For a triangle-free graph G, let h₄(G) be the smallest number of edges that need to
be added to G so that it has diameter at most 4 and is still triangle-free.

Is it true that there exists a constant c > 0 such that for every connected
triangle-free graph G on n vertices, h₄(G) < (1 - c) · n?
-/
theorem erdos_problem_619 :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      G.Connected →
      (triangleFreeDiamCompletion 4 G : ℝ) < (1 - c) * (n : ℝ) :=
  sorry

end
