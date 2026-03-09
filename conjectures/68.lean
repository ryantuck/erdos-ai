import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Topology

/--
Erdős Problem #68 [Er68d, Er88c, Er90, Er97e, Er97f]:

Is the sum ∑_{n≥2} 1/(n! - 1) irrational?

Erdős notes that ∑ 1/(n! + t) should be transcendental for every integer t.
Weisenberg observed that this sum can also be written as ∑_{k≥1} ∑_{n≥2} 1/(n!)^k.
-/
theorem erdos_problem_68 :
    Irrational (∑' (n : ℕ), if n < 2 then 0 else (1 : ℝ) / (n.factorial - 1)) :=
  sorry
