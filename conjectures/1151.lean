import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section
open Classical Finset BigOperators

namespace Erdos1151

/-- The k-th Chebyshev node of order n (0-indexed):
    cos((2k + 1)π / (2n)) for k = 0, ..., n-1. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))

/-- The Lagrange basis polynomial ℓ_i(x) = ∏_{j≠i} (x - x_j)/(x_i - x_j). -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x - nodes j) / (nodes i - nodes j)

/-- The Lagrange interpolation of f at the given nodes, evaluated at x:
    L(x) = ∑_i f(x_i) · ℓ_i(x). -/
noncomputable def lagrangeInterp {n : ℕ} (nodes : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (nodes i) * lagrangeBasis nodes i x

/-- The set of limit points (cluster points) of a sequence of reals.
    A real y is a limit point of a if for every ε > 0 and every N,
    there exists n ≥ N with |a(n) - y| < ε. -/
def limitPoints (a : ℕ → ℝ) : Set ℝ :=
  {y : ℝ | ∀ ε > 0, ∀ N : ℕ, ∃ n, N ≤ n ∧ |a n - y| < ε}

/-!
# Erdős Problem #1151

Let $\mathcal{L}^n f(x) = \sum_{i} f(a_i) \ell_i(x)$ be the Lagrange interpolation
polynomial of degree $n-1$ agreeing with $f$ at the $n$ Chebyshev nodes.

Prove that for any $x \in [-1,1]$ and any closed $A \subseteq [-1,1]$, there exists a
continuous function $f$ such that $A$ is exactly the set of limit points of the sequence
$\mathcal{L}^n f(x)$ as $n \to \infty$.

Erdős [Er41] proved that for $x = \cos(\pi p/q)$ with $p, q$ odd, there is a continuous
$f$ with $\lim_{n \to \infty} \mathcal{L}^n f(x) = \infty$. In [Er43] he claims
(without proof) that for any closed set $A$ there exists continuous $f$ achieving $A$
as the limit set.

Tags: analysis, polynomials
-/

/--
Erdős Problem #1151 [Va99, 2.41]:
For any x ∈ [-1,1] and any closed A ⊆ [-1,1], there exists a continuous
function f such that A is the set of limit points of the Lagrange interpolation
polynomials Lⁿf(x) at the Chebyshev nodes as n → ∞.
-/
theorem erdos_problem_1151 (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (A : Set ℝ) (hA : IsClosed A) (hAsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      limitPoints (fun n => lagrangeInterp (chebyshevNode (n + 1)) f x) = A :=
  sorry

end Erdos1151
