import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Filter Set Finset

/-!
# Erdős Problem #671

Given nodes $a_i^n \in [-1,1]$ for $1 \leq i \leq n$, define $p_i^n$ as the
Lagrange basis polynomial of degree $n-1$ (satisfying $p_i^n(a_i^n) = 1$ and
$p_i^n(a_j^n) = 0$ for $j \neq i$) and the Lagrange interpolation operator
$$\mathcal{L}^n f(x) = \sum_i f(a_i^n) p_i^n(x).$$

Part 1: Is there a triangular array of nodes in $[-1,1]$ such that for every
continuous $f: [-1,1] \to \mathbb{R}$ there exists $x \in [-1,1]$ where the
Lebesgue function $\sum_i |p_i^n(x)|$ has infinite limsup yet
$\mathcal{L}^n f(x) \to f(x)$?

Part 2: Is there such an array where the Lebesgue function has infinite limsup
for every $x \in [-1,1]$ and yet for every continuous $f$ there exists $x$ with
$\mathcal{L}^n f(x) \to f(x)$?
-/

/-- The value of the i-th Lagrange basis polynomial for nodes `a` at point `x`.
    This is ∏_{j ≠ i} (x - a_j) / (a_i - a_j). -/
noncomputable def lagrangeBasisEval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ univ.erase i, (x - a j) / (a i - a j)

/-- The Lebesgue function: Λ_n(x) = ∑_i |p_i^n(x)|. -/
noncomputable def lebesgueFunction {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |lagrangeBasisEval a i x|

/-- The Lagrange interpolation of `f` at nodes `a`, evaluated at `x`:
    L^n f(x) = ∑_i f(a_i) · p_i(x). -/
noncomputable def lagrangeInterpolation {n : ℕ} (a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (a i) * lagrangeBasisEval a i x

/--
Erdős Problem #671 (Part 1): There exists a triangular array of distinct nodes
in [-1,1] such that for every continuous f : [-1,1] → ℝ, there exists x ∈ [-1,1]
where the Lebesgue function has infinite limsup yet the Lagrange interpolation
converges to f(x).
-/
theorem erdos_problem_671_part1 :
    ∃ (nodes : (n : ℕ) → Fin n → ℝ),
      (∀ n (i : Fin n), nodes n i ∈ Icc (-1 : ℝ) 1) ∧
      (∀ n, Function.Injective (nodes n)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ x ∈ Icc (-1 : ℝ) 1,
          (∀ M : ℝ, ∃ᶠ n in atTop, lebesgueFunction (nodes n) x ≥ M) ∧
          Tendsto (fun n => lagrangeInterpolation (nodes n) f x) atTop (nhds (f x)) :=
  sorry

/--
Erdős Problem #671 (Part 2): There exists a triangular array of distinct nodes
in [-1,1] such that the Lebesgue function has infinite limsup at every x ∈ [-1,1],
and yet for every continuous f : [-1,1] → ℝ there exists x ∈ [-1,1] where the
Lagrange interpolation converges to f(x).
-/
theorem erdos_problem_671_part2 :
    ∃ (nodes : (n : ℕ) → Fin n → ℝ),
      (∀ n (i : Fin n), nodes n i ∈ Icc (-1 : ℝ) 1) ∧
      (∀ n, Function.Injective (nodes n)) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ∀ M : ℝ,
        ∃ᶠ n in atTop, lebesgueFunction (nodes n) x ≥ M) ∧
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ x ∈ Icc (-1 : ℝ) 1,
          Tendsto (fun n => lagrangeInterpolation (nodes n) f x) atTop (nhds (f x))) :=
  sorry
