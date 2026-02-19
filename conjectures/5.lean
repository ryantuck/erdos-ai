import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

open Filter Topology Nat Real

/--
Erdős's conjecture on the distribution of prime gaps (Problem #5).
The set of limit points of (p_{n+1} - p_n) / log n is [0, ∞].
This is formalized as: for every C ≥ 0, C is a cluster point of the sequence as n → ∞.
-/
theorem erdos_problem_5_conjecture :
  ∀ C : ℝ, C ≥ 0 → MapClusterPt C atTop (fun n => ((nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ)) / log (n : ℝ)) :=
sorry
