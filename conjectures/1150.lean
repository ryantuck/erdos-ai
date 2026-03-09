import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
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
Erdős Problem #1150 [Ha74,4.31] [Va99,2.36]:

Does there exist a constant c > 0 such that, for all large n and all polynomials P
of degree n with coefficients ±1,
  max_{|z|=1} |P(z)| > (1+c)√n?

In other words, does there exist an 'ultraflat' polynomial with coefficients ±1?
The lower bound max_{|z|=1} |P(z)| ≥ √n is trivial from Parseval's theorem.
The answer is yes (ultraflat unimodular polynomials exist) if the coefficients can
take any values on the unit circle (see [230]), but this problem asks specifically
about ±1 coefficients.
-/
theorem erdos_problem_1150 :
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ ε : Fin (n + 1) → ℤ,
          IsLittlewoodCoeff n ε →
          ∃ z : ℂ, ‖z‖ = 1 ∧
            (1 + c) * Real.sqrt n < ‖evalLittlewood n ε z‖ :=
  sorry

end
