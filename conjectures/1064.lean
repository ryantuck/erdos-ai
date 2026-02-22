import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Asymptotics.Defs

open Set Filter Finset

/-!
# Erdős Problem #1064

Prove that φ(n) > φ(n - φ(n)) for almost all n, but that φ(n) < φ(n - φ(n))
for infinitely many n, where φ is Euler's totient function.

Luca and Pomerance [LuPo02] proved that the set of n with φ(n) > φ(n - φ(n))
has natural density 1. They also proved that for any function f(n) = o(n),
φ(n) > φ(n - φ(n)) + f(n) for almost all n, and that for any constant c > 0,
the inequality φ(n) < c · φ(n - φ(n)) holds for infinitely many n.
-/

/--
Erdős Problem #1064, Part 1 [Er80f]:

The set of n with φ(n) > φ(n - φ(n)) has natural density 1.
-/
theorem erdos_problem_1064_density :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n =>
          Nat.totient (n - Nat.totient n) < Nat.totient n)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1064, Part 2 [Er80f]:

There are infinitely many n with φ(n) < φ(n - φ(n)).
-/
theorem erdos_problem_1064_infinite :
    Set.Infinite {n : ℕ | Nat.totient n < Nat.totient (n - Nat.totient n)} :=
  sorry

/--
Luca-Pomerance strengthening [LuPo02]:

For any function f : ℕ → ℕ with f(n) = o(n), we have
φ(n) > φ(n - φ(n)) + f(n) for almost all n.
-/
theorem erdos_problem_1064_strengthened (f : ℕ → ℕ)
    (hf : Asymptotics.IsLittleO Filter.atTop
      (fun n => (f n : ℝ)) (fun n => (n : ℝ))) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n =>
          Nat.totient (n - Nat.totient n) + f n < Nat.totient n)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) :=
  sorry
