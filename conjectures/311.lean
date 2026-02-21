import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset Real

/-!
# Erdős Problem #311

Let δ(N) be the minimal non-zero value of |1 - Σ_{n ∈ A} 1/n| as A ranges over
all subsets of {1, ..., N}. Is it true that δ(N) = e^{-(c+o(1))N} for some
constant c ∈ (0, 1)?

It is trivially known that δ(N) ≥ 1/lcm(1,...,N) = e^{-(1+o(1))N}, so c ≤ 1.
Tang has shown δ(N) ≤ exp(-c·N/(log N · log log N)³) for some c > 0.
-/

/-- The minimal non-zero value of |1 - Σ_{n ∈ A} 1/n| as A ranges over all
    subsets of {1, ..., N}. -/
noncomputable def unitFractionDeviation (N : ℕ) : ℝ :=
  sInf { x : ℝ | x > 0 ∧ ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    x = |1 - ∑ n ∈ A, (1 : ℝ) / n| }

/--
Erdős Problem #311 [ErGr80, p.40]:

Let δ(N) be the minimal non-zero value of |1 - Σ_{n ∈ A} 1/n| as A ranges over
all subsets of {1, ..., N}. The conjecture asserts that δ(N) = e^{-(c+o(1))N}
for some constant c ∈ (0, 1).

Equivalently, there exists c ∈ (0, 1) such that for all ε > 0 and all
sufficiently large N:
  exp(-(c + ε) · N) ≤ δ(N) ≤ exp(-(c - ε) · N).
-/
theorem erdos_problem_311 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      exp (-(c + ε) * N) ≤ unitFractionDeviation N ∧
      unitFractionDeviation N ≤ exp (-(c - ε) * N) :=
  sorry
