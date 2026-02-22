import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #618

For a triangle-free graph $G$ on $n$ vertices, let $h_2(G)$ be the smallest number
of edges that need to be added to $G$ so that it has diameter $2$ and is still
triangle-free. Is it true that if $G$ has maximum degree $o(n^{1/2})$ then
$h_2(G) = o(n^2)$?

A problem of Erdős, Gyárfás, and Ruszinkó [EGR98].

Simonovits showed that there exist graphs $G$ with maximum degree $\gg n^{1/2}$
and $h_2(G) \gg n^2$.

Proved in the affirmative by Alon.

Tags: graph theory
-/

/-- `triangleFreeDiam2Completion G` is the minimum number of edges that must be added
    to a triangle-free graph `G` on `Fin n` so that the resulting supergraph has
    diameter at most 2 and remains triangle-free. -/
noncomputable def triangleFreeDiam2Completion {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph (Fin n), G ≤ H ∧
    H.CliqueFree 3 ∧
    H.Connected ∧
    H.diam ≤ 2 ∧
    (H.edgeFinset \ G.edgeFinset).card = k}

/--
**Erdős Problem #618** [EGR98][Er99]:

For a triangle-free graph G, let h₂(G) be the smallest number of edges that need
to be added to G so that it has diameter 2 and is still triangle-free. If G has
maximum degree o(n^{1/2}) then h₂(G) = o(n²).

Formulated as: for every ε > 0, there exist δ > 0 and N₀ such that for all n ≥ N₀,
for every triangle-free graph G on n vertices with every vertex having degree at most
δ · n^{1/2}, we have h₂(G) ≤ ε · n².

Proved by Alon.
-/
theorem erdos_problem_618 :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (∀ v : Fin n, (G.degree v : ℝ) ≤ δ * (n : ℝ) ^ ((1 : ℝ) / 2)) →
      (triangleFreeDiam2Completion G : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry

end
