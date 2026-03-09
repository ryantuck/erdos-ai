import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring

open Nat

/--
Erdős Problem #972 [Er65b]:

Let α > 1 be irrational. Are there infinitely many primes p such that
⌊pα⌋ is also prime?
-/
theorem erdos_problem_972
    (α : ℝ) (hα_irr : Irrational α) (hα_gt : α > 1) :
    ∀ N : ℕ, ∃ p : ℕ, p ≥ N ∧ p.Prime ∧ (⌊(p : ℝ) * α⌋).toNat.Prime :=
  sorry
