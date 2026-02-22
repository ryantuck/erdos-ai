import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset Real

noncomputable section

/-!
# Erdős Problem #787

Let g(n) be maximal such that given any set A ⊂ ℝ with |A| = n there exists
some B ⊆ A of size |B| ≥ g(n) such that b₁ + b₂ ∉ A for all b₁ ≠ b₂ ∈ B.

Estimate g(n).

The current best bounds are
  (log n)^{1+c} ≪ g(n) ≪ exp(√(log n))
for some constant c > 0, the lower bound due to Sanders [Sa21] and the upper
bound due to Ruzsa [Ru05]. Beker [Be25] proved the lower bound with c = 1/68.

https://www.erdosproblems.com/787

Tags: additive combinatorics
-/

/-- A subset B of a finite set A ⊆ ℝ is *sum-avoiding in A* if B ⊆ A and
    for all distinct b₁, b₂ ∈ B, their sum b₁ + b₂ is not in A. -/
def IsSumAvoidingIn (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ + b₂ ∉ A

/-- g(n): the largest m such that every n-element subset of ℝ contains a
    sum-avoiding subset of size at least m. -/
noncomputable def erdos787_g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsSumAvoidingIn A B ∧ B.card ≥ m}

/--
**Erdős Problem #787** — Lower bound (Sanders [Sa21], Beker [Be25]):

There exists a constant c > 0 such that g(n) ≫ (log n)^{1+c} for all
sufficiently large n.
-/
theorem erdos_problem_787_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos787_g n : ℝ) ≥ C * (Real.log (n : ℝ)) ^ (1 + c) :=
  sorry

/--
**Erdős Problem #787** — Upper bound (Ruzsa [Ru05]):

g(n) ≪ exp(√(log n)) for all sufficiently large n.
-/
theorem erdos_problem_787_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos787_g n : ℝ) ≤ C * Real.exp (Real.sqrt (Real.log (n : ℝ))) :=
  sorry

end
