import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Set

/-!
# Erdős Problem #457

Is there some ε > 0 such that there are infinitely many n where all primes
p ≤ (2 + ε) log n divide ∏_{1 ≤ i ≤ log n} (n + i)?

A problem of Erdős and Pomerance.
-/

/-- The product ∏_{1 ≤ i ≤ ⌊log n⌋} (n + i). -/
noncomputable def consecutiveProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 (Nat.floor (Real.log n)), (n + i)

/--
Erdős Problem #457 [Er79d] [ErGr80, p.91]:
Is there some ε > 0 such that there are infinitely many n where all primes
p ≤ (2 + ε) log n divide ∏_{1 ≤ i ≤ ⌊log n⌋} (n + i)?
-/
theorem erdos_problem_457 :
    ∃ ε : ℝ, 0 < ε ∧
      Set.Infinite {n : ℕ | ∀ p : ℕ, Nat.Prime p →
        (p : ℝ) ≤ (2 + ε) * Real.log n →
        p ∣ consecutiveProduct n} :=
  sorry
