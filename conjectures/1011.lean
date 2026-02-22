import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Filter

noncomputable section

/-!
# Erdős Problem #1011

Let $f_r(n)$ be minimal such that every graph on $n$ vertices with $\geq f_r(n)$
edges and chromatic number $\geq r$ contains a triangle. Determine $f_r(n)$.

Turán's theorem implies $f_2(n) = \lfloor n^2/4 \rfloor + 1$.
Erdős and Gallai proved $f_3(n) = \lfloor (n-1)^2/4 \rfloor + 2$.

Simonovits showed $f_r(n) = n^2/4 - g(r)/2 \cdot n + O(1)$, where $g(r)$ is
the largest $m$ such that any triangle-free graph with chromatic number $\geq r$
requires removing at least $m$ vertices to become bipartite.

The best known bounds on $g(r)$ are
$(1/2 - o(1)) r^2 \log r \leq g(r) \leq (2 + o(1)) r^2 \log r$.
The lower bound follows from Davies–Illingworth, and the upper bound from
Hefty–Horn–King–Pfender.

Tags: graph theory
-/

/-- `erdos1011_f r n` is the minimum number of edges `m` such that every
    graph on `n` vertices with at least `m` edges and chromatic number `≥ r`
    contains a triangle (3-clique). -/
def erdos1011_f (r n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard ≥ m → (r : ℕ∞) ≤ G.chromaticNumber → ¬G.CliqueFree 3}

/--
**Erdős Problem #1011** [Er71] — Simonovits asymptotic:

For every `r ≥ 2` there exist `g_r : ℝ` and `C ≥ 0` such that, for all
sufficiently large `n`,

  `|f_r(n) - (n² / 4 - g_r / 2 · n)| ≤ C`.

Simonovits established this asymptotic form. The open problem is to determine
`g_r` precisely; the best known bounds give `g_r ≍ r² log r`.
-/
theorem erdos_problem_1011 :
    ∀ r : ℕ, r ≥ 2 →
      ∃ (g_r : ℝ) (C : ℝ), 0 ≤ C ∧
        ∀ᶠ n in atTop,
          |(erdos1011_f r n : ℝ) - ((n : ℝ) ^ 2 / 4 - g_r / 2 * (n : ℝ))| ≤ C :=
  sorry

end
