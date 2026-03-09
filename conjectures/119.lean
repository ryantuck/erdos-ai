import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex Finset BigOperators

noncomputable section

/--
The product polynomial p_n(z) = ∏_{i<n} (z - z_i) for a sequence on the unit circle.
-/
def prodPoly (z_seq : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ range n, (z - z_seq i)

/--
M_n = sup_{|z|=1} |p_n(z)|, the maximum modulus of p_n on the unit circle.
-/
def maxModulus (z_seq : ℕ → ℂ) (n : ℕ) : ℝ :=
  ⨆ (z : ℂ) (_ : ‖z‖ = 1), ‖prodPoly z_seq n z‖

/--
Erdős Problem #119 (part 1) - Proved by Wagner [Wa80]:

For any sequence z_i on the unit circle, limsup M_n = ∞.
Equivalently, M_n is unbounded.
-/
theorem erdos_problem_119a :
    ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
      ∀ B : ℝ, ∃ n : ℕ, maxModulus z_seq n > B :=
  sorry

/--
Erdős Problem #119 (part 2) - Proved by Beck [Be91]:

There exists c > 0 such that for any sequence z_i on the unit circle,
max_{n ≤ N} M_n > N^c.
-/
theorem erdos_problem_119b :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
        ∀ N : ℕ, 0 < N →
          ∃ n : ℕ, n ≤ N ∧ maxModulus z_seq n > (N : ℝ) ^ c :=
  sorry

/--
Erdős Problem #119 (part 3) - OPEN, $100:

There exists c > 0 such that for any sequence z_i on the unit circle
and all sufficiently large n, ∑_{k ≤ n} M_k > n^{1+c}.
-/
theorem erdos_problem_119c :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          ∑ k ∈ range (n + 1), maxModulus z_seq k > (n : ℝ) ^ (1 + c) :=
  sorry

end
