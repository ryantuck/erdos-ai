import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.LiminfLimsup

open Filter Topology

/-- The auxiliary sequence u₀ = 1, u_{n+1} = uₙ(uₙ + 1),
    giving 1, 2, 6, 42, 1806, ... -/
def sylvesterU : ℕ → ℕ
  | 0 => 1
  | n + 1 => sylvesterU n * (sylvesterU n + 1)

/-- The Sylvester sequence sₙ = uₙ + 1, giving 2, 3, 7, 43, 1807, ...
    This is the greedy Egyptian fraction representation of 1:
    ∑ₙ 1/sₙ = 1. -/
def sylvesterSeq (n : ℕ) : ℕ := sylvesterU n + 1

/--
Erdős Problem #315 (Erdős–Graham, 1980):

The Sylvester sequence (2, 3, 7, 43, 1807, ...) is defined by s₀ = 2 and
s_{n+1} = sₙ² - sₙ + 1. It satisfies ∑ 1/sₙ = 1 and
lim sₙ^{1/2ⁿ} = c₀ ≈ 1.264085... (the Vardi constant).

The conjecture states: if a₀ < a₁ < a₂ < ... is any strictly increasing
sequence of positive integers with ∑ 1/aₙ = 1, other than the Sylvester
sequence, then liminf aₙ^{1/2ⁿ} < c₀. In other words, the Sylvester (greedy)
representation uniquely maximizes the growth rate liminf.

This was proved independently by Kamio [Ka25] and Li–Tang [LiTa25].
-/
theorem erdos_problem_315 :
    ∀ (a : ℕ → ℕ),
      StrictMono a →
      (∀ n, 0 < a n) →
      HasSum (fun n => (1 : ℝ) / (a n : ℝ)) 1 →
      a ≠ sylvesterSeq →
      Filter.liminf (fun n => ((a n : ℝ)) ^ ((2 : ℝ) ^ (n : ℕ))⁻¹) atTop <
        Filter.liminf (fun n => ((sylvesterSeq n : ℝ)) ^ ((2 : ℝ) ^ (n : ℕ))⁻¹) atTop :=
  sorry
