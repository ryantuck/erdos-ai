import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #751

Let $G$ be a graph with chromatic number $χ(G) = 4$. If $m_1 < m_2 < \cdots$ are the
lengths of the cycles in $G$, can $\min(m_{i+1} - m_i)$ be arbitrarily large? Can this
happen if the girth of $G$ is large?

The answer is no: Bondy and Vince [BoVi98] proved that every graph with minimum degree
at least $3$ has two cycles whose lengths differ by at most $2$, and hence the same is
true for every graph with chromatic number $4$.
-/

/-- The set of cycle lengths occurring in a simple graph. -/
def SimpleGraph.cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/-- **Bondy–Vince Theorem (Erdős Problem #751)**: Every graph with minimum degree at
least 3 contains two cycles whose lengths differ by at most 2. This resolves
Erdős Problem #751 in the negative: for every graph with chromatic number 4, the gaps
between consecutive cycle lengths cannot be made arbitrarily large. -/
theorem erdos_problem_751 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    ∃ m₁ ∈ G.cycleLengths, ∃ m₂ ∈ G.cycleLengths,
      m₁ < m₂ ∧ m₂ - m₁ ≤ 2 :=
  sorry

end
