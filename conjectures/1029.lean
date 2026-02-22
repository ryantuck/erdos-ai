import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

noncomputable section

/-!
# Erdős Problem #1029

If R(k) is the Ramsey number for K_k, the minimal n such that every 2-colouring
of the edges of K_n contains a monochromatic copy of K_k, then

  R(k) / (k · 2^{k/2}) → ∞.

Erdős and Szekeres [ErSz35] proved k·2^{k/2} ≪ R(k) ≤ C(2k−1,k−1).
The probabilistic method gives R(k) ≥ (1+o(1))·(1/(√2·e))·k·2^{k/2},
improved by Spencer [Sp75] to R(k) ≥ (1+o(1))·(√2/e)·k·2^{k/2}.
-/

/-- The diagonal Ramsey number R(k): the minimum N such that for every
    symmetric 2-colouring of the edges of K_N, there is a monochromatic
    clique of size k in some colour. -/
noncomputable def diagonalRamseyNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (S : Finset (Fin N)), S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b}

/--
Erdős Problem #1029 [Er93, p.337]:

R(k) / (k · 2^{k/2}) → ∞ as k → ∞.

Formulated as: for every C > 0, there exists K₀ such that for all k ≥ K₀,
  R(k) ≥ C · k · 2^{k/2}.
-/
theorem erdos_problem_1029 :
    ∀ C : ℝ, C > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (diagonalRamseyNumber k : ℝ) ≥ C * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) :=
  sorry

end
