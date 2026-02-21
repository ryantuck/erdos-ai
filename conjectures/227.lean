import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Order.Basic

open Complex Filter Topology

noncomputable section

/--
The maximum term of a power series with coefficients `a` at radius `r`:
μ(r) = sup_n ‖aₙ‖ · r^n
-/
def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖a n‖ * r ^ n

/--
The maximum modulus of `f` on the circle of radius `r`:
M(r) = sup { ‖f(z)‖ | ‖z‖ = r }
-/
def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/--
Erdős Problem #227 (DISPROVED):
Let f = ∑ aₙzⁿ be an entire function which is not a polynomial. Is it true that if
  lim_{r→∞} (max_n |aₙ|rⁿ) / (max_{|z|=r} |f(z)|)
exists then it must be 0?

This was disproved by Clunie and Hayman [ClHa64], who showed that the limit can take
any value in [0, 1/2].
-/
theorem erdos_problem_227 :
  ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
    (∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) →
    (∀ N : ℕ, ∃ n, N < n ∧ a n ≠ 0) →
    ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus f r) atTop (𝓝 L) →
    L = 0 :=
sorry
