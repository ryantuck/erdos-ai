import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1078

Let G be an r-partite graph with n vertices in each part. If G has minimum degree
≥ (r - 3/2 - o(1))n then G must contain a K_r.

A conjecture of Bollobás, Erdős, and Szemerédi [BES75b], who proved that
r - 3/2 would be the best possible here. This was proved by Haxell [Ha01].
The sharp threshold of (r-1)n - ⌈sn/(2s-1)⌉ where s = ⌊r/2⌋ was proved
by Haxell and Szabó [HaSz06].

https://www.erdosproblems.com/1078

Tags: graph theory
-/

/-- An r-partite graph on vertex set Fin r × Fin n: no edges within any part. -/
def IsMultipartite {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∀ (i : Fin r) (a b : Fin n), ¬G.Adj (i, a) (i, b)

/-- A transversal clique in an r-partite graph: a choice of one vertex from each
    part such that all chosen vertices are pairwise adjacent. This corresponds
    to a copy of K_r in an r-partite graph. -/
def HasTransversalClique {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∃ f : Fin r → Fin n, ∀ i j : Fin r, i ≠ j → G.Adj (i, f i) (j, f j)

/--
Erdős Problem #1078 [BES75, Er75]:

For all r ≥ 2, for every ε > 0, there exists n₀ such that for all n ≥ n₀,
every r-partite graph G with n vertices in each part and minimum degree
≥ (r - 3/2 - ε) · n contains a transversal clique K_r.

The o(1) term in the original statement is formalized as: for every ε > 0,
there exists a threshold n₀ beyond which the conclusion holds.

Bollobás, Erdős, and Szemerédi proved that r - 3/2 is best possible.
Proved by Haxell [Ha01].
-/
theorem erdos_problem_1078 (r : ℕ) (hr : r ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin r × Fin n)) [DecidableRel G.Adj],
      IsMultipartite G →
      (∀ v : Fin r × Fin n, (G.degree v : ℝ) ≥ ((r : ℝ) - 3 / 2 - ε) * (n : ℝ)) →
      HasTransversalClique G :=
  sorry

end
