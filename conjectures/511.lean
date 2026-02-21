import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Erdős Problem #511 (DISPROVED)

Let $f(z) \in \mathbb{C}[z]$ be a monic polynomial of degree $n$. Is it true that,
for every $c > 1$, the set $\{z \in \mathbb{C} : |f(z)| < 1\}$ has at most $O_c(1)$
many connected components of diameter $> c$ (where the implied constant is
independent of $n$)?

Disproved by Pommerenke, who showed that for any $0 < d < 4$ and $k \geq 1$,
there exist monic polynomials $f \in \mathbb{C}[x]$ such that
$\{z : |f(z)| \leq 1\}$ has at least $k$ connected components of diameter $\geq d$.
-/

open Polynomial Set

/-- Erdős Problem #511: For every c > 1, there exists a bound M (independent of the
    degree) such that for any monic polynomial f ∈ ℂ[z], the sublevel set
    {z ∈ ℂ : ‖f(z)‖ < 1} has at most M connected components of diameter > c. -/
theorem erdos_problem_511 :
    ∀ c : ℝ, c > 1 →
      ∃ M : ℕ, ∀ (f : Polynomial ℂ),
        f.Monic →
          ∀ (k : ℕ) (C : Fin k → Set ℂ),
            (∀ i, (C i).Nonempty) →
            (∀ i, C i ⊆ {z : ℂ | ‖Polynomial.eval z f‖ < 1}) →
            (∀ i, IsPreconnected (C i)) →
            (∀ i, Metric.diam (C i) > c) →
            (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
            k ≤ M := by
  sorry
