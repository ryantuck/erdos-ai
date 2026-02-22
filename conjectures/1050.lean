import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #1050

Is ∑_{n=1}^∞ 1/(2^n - 3) irrational?

Erdős [Er48] proved that ∑ 1/(2^n - 1) = ∑ τ(n)/2^n is irrational (where
τ(n) is the divisor function). He notes [Er88c] that ∑ 1/(2^n + t) should be
transcendental for every integer t (with the obvious exception t = 0).

This was proved by Borwein [Bo91], who more generally proved that, for any
integer q ≥ 2 and rational r ≠ 0 (distinct from -q^n for all n ≥ 1), the
series ∑_{n=1}^∞ 1/(q^n + r) is irrational.
-/

/--
Erdős Problem #1050 [ErGr80,p.62] [Er88c,p.102]:

The sum ∑_{n=1}^∞ 1/(2^n - 3) is irrational.

Proved by Borwein [Bo91].
-/
theorem erdos_problem_1050 :
    Irrational (∑' (n : ℕ), (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) :=
  sorry

end
