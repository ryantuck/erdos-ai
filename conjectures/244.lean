import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.Real

open Classical Nat Real Filter

noncomputable section

/--
The set of positive integers that can be written as p + ⌊C^k⌋ for some
prime p and some k ≥ 0.
-/
def erdos244Set (C : ℝ) : Set ℕ :=
  {n : ℕ | ∃ (p k : ℕ), Nat.Prime p ∧ n = p + ⌊C ^ k⌋₊}

/--
The lower density of a set S ⊆ ℕ:
  lim inf_{N → ∞} |S ∩ {0, ..., N-1}| / N
-/
noncomputable def lowerDensity244 (S : Set ℕ) : ℝ :=
  Filter.liminf
    (fun N : ℕ => ((Finset.range N).filter (· ∈ S)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #244 [Er61,p.230]:

Let C > 1. Does the set of integers of the form p + ⌊C^k⌋, for some prime p
and k ≥ 0, have positive density?

Originally asked to Erdős by Kalmár. Erdős believed the answer is yes.
Romanoff [Ro34] proved that the answer is yes when C is an integer.
Ding [Di25] has proved that this is true for almost all C > 1.
-/
theorem erdos_problem_244 (C : ℝ) (hC : 1 < C) :
    lowerDensity244 (erdos244Set C) > 0 :=
  sorry

end
