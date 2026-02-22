import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

noncomputable section
open SimpleGraph Classical

/-!
# Erdős Problem #934

Let $h_t(d)$ be minimal such that every graph $G$ with $h_t(d)$ edges and
maximal degree $\leq d$ contains two edges whose shortest path between them
has length $\geq t$.

Estimate $h_t(d)$.

A problem of Erdős and Nešetřil [Er88]. Known:
- $h_t(d) \leq 2d^t$ always and $h_1(d) = d + 1$
- $h_2(d) \leq \frac{5}{4}d^2 + 1$ (Chung–Gyárfás–Tuza–Trotter [CGTT90])
- $h_t(d) \leq \frac{3}{2}d^t + 1$ for all $t \geq 1$ [CCJK22]

Cambie–Cames van Batenburg–de Joannis de Verclos–Kang [CCJK22] conjecture
that, for all $t \geq 3$, $h_t(d) \sim d^t$ as $d \to \infty$:
$h_t(d) \leq (1 + o(1))d^t$ for all $d$ and
$h_t(d) \geq (1 - o(1))d^t$ for infinitely many $d$.

https://www.erdosproblems.com/934
-/

/-- Two edges e₁, e₂ in a simple graph G are at distance at least t:
    for every endpoint u of e₁ and v of e₂ that lie in the same connected
    component, t ≤ G.dist u v.  (Endpoints in different components are
    considered infinitely far apart and satisfy any finite distance bound.) -/
def EdgesAtDist {V : Type*} (G : SimpleGraph V) (e₁ e₂ : Sym2 V) (t : ℕ) : Prop :=
  ∀ u, u ∈ e₁ → ∀ v, v ∈ e₂ → G.Reachable u v → t ≤ G.dist u v

/-- Erdős Problem #934, upper bound direction of the asymptotic conjecture:
    For all t ≥ 3 and ε > 0, for all sufficiently large d, every finite graph
    with maximum degree ≤ d and more than (1 + ε) · d^t edges contains two
    distinct edges at distance ≥ t. -/
theorem erdos_problem_934 :
    ∀ t : ℕ, 3 ≤ t →
    ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ d : ℕ, D₀ ≤ d →
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.maxDegree ≤ d →
      (G.edgeFinset.card : ℝ) > (1 + ε) * (d : ℝ) ^ t →
      ∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet,
        e₁ ≠ e₂ ∧ EdgesAtDist G e₁ e₂ t :=
  sorry

/-- Erdős Problem #934, lower bound direction of the asymptotic conjecture:
    For all t ≥ 3 and ε > 0, there are infinitely many d for which some graph
    with maximum degree ≤ d and at least (1 - ε) · d^t edges has no pair of
    distinct edges at distance ≥ t. -/
theorem erdos_problem_934_lower :
    ∀ t : ℕ, 3 ≤ t →
    ∀ ε : ℝ, 0 < ε →
    ∀ D₀ : ℕ, ∃ d : ℕ, D₀ ≤ d ∧
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ d ∧
      (G.edgeFinset.card : ℝ) ≥ (1 - ε) * (d : ℝ) ^ t ∧
      ¬∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet,
        e₁ ≠ e₂ ∧ EdgesAtDist G e₁ e₂ t :=
  sorry

end
