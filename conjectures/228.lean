import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

noncomputable section

/--
A Littlewood polynomial of degree n is a polynomial with all coefficients in {-1, +1}.
We represent it as a function ε : Fin (n + 1) → ℤ with each ε i ∈ {-1, 1}, and its
evaluation at z ∈ ℂ is ∑ i, ε i * z ^ (i : ℕ).
-/
def IsLittlewoodCoeff (n : ℕ) (ε : Fin (n + 1) → ℤ) : Prop :=
  ∀ i, ε i = -1 ∨ ε i = 1

def evalLittlewood (n : ℕ) (ε : Fin (n + 1) → ℤ) (z : ℂ) : ℂ :=
  ∑ i : Fin (n + 1), (ε i : ℂ) * z ^ (i : ℕ)

/--
Erdős Problem #228 [Er57, Er61, Va99] (Littlewood's conjecture on flat polynomials):

Does there exist, for all large n, a polynomial P of degree n, with coefficients ±1,
such that √n ≪ |P(z)| ≪ √n for all |z| = 1, with the implied constants independent
of z and n?

The answer is yes (for all n ≥ 2), proved by Balister, Bollobás, Morris, Sahasrabudhe,
and Tiba (2020).
-/
theorem erdos_problem_228 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ ε : Fin (n + 1) → ℤ,
          IsLittlewoodCoeff n ε ∧
          ∀ z : ℂ, ‖z‖ = 1 →
            c * Real.sqrt n ≤ ‖evalLittlewood n ε z‖ ∧
            ‖evalLittlewood n ε z‖ ≤ C * Real.sqrt n :=
  sorry

end
