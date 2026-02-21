import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #451

Estimate n_k, the smallest integer > 2k such that ∏_{1 ≤ i ≤ k} (n_k - i)
has no prime factor in (k, 2k).

Erdős and Graham proved n_k > k^{1+c} for some constant c > 0.
Erdős conjectures that n_k > k^d for all constant d, and n_k < e^{o(k)}.
-/

/-- The product (n-1)(n-2)⋯(n-k) has no prime factor p with k < p < 2k. -/
def noInteriorPrimeFactor (k n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → k < p → p < 2 * k →
    ¬(p ∣ ∏ i ∈ Finset.Icc 1 k, (n - i))

/-- n_k: the smallest integer > 2k such that the product (n-1)(n-2)⋯(n-k)
    has no prime factor in (k, 2k). Returns 0 if no such integer exists. -/
noncomputable def erdos451_nk (k : ℕ) : ℕ :=
  if h : ∃ n, 2 * k < n ∧ noInteriorPrimeFactor k n
  then Nat.find h
  else 0

/--
Erdős Problem #451 [Er79d][ErGr80, p.89]:

n_k grows superpolynomially but subexponentially:
  (1) For all d > 0, n_k > k^d for all sufficiently large k.
  (2) For all ε > 0, n_k < e^{ε·k} for all sufficiently large k.
-/
theorem erdos_problem_451 :
    (∀ d : ℝ, 0 < d → ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (k : ℝ) ^ d < (erdos451_nk k : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
      (erdos451_nk k : ℝ) < Real.exp (ε * (k : ℝ))) :=
  sorry

end
