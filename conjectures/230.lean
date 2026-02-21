import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #230

Let P(z) = ∑_{k=1}^{n} a_k z^k with a_k ∈ ℂ and |a_k| = 1 for all k.
Does there exist a constant c > 0 such that, for n ≥ 2,
  max_{|z|=1} |P(z)| ≥ (1+c)√n?

The lower bound of √n is trivial from Parseval's theorem.

DISPROVED: Kahane [Ka80] constructed 'ultraflat' polynomials with unimodular
coefficients such that |P(z)| = (1+o(1))√n uniformly on the unit circle.
Bombieri and Bourgain [BoBo09] later improved the error term.
-/

/--
Erdős Problem #230 [Er57, Er61, Er80h] (DISPROVED):

The original conjecture asked whether there exists c > 0 such that every
polynomial P(z) = ∑_{k=1}^{n} a_k z^k with unimodular coefficients
(|a_k| = 1) satisfies max_{|z|=1} |P(z)| ≥ (1+c)√n.

Kahane [Ka80] disproved this by constructing 'ultraflat' polynomials where
|P(z)| = (1+o(1))√n uniformly on the unit circle.

Formalized as the negation: for every ε > 0 and all sufficiently large n,
there exists a polynomial with unimodular coefficients whose maximum modulus
on the unit circle is at most (1 + ε)√n.
-/
theorem erdos_problem_230 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a : Fin n → ℂ,
      (∀ k : Fin n, ‖a k‖ = 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖∑ k : Fin n, a k * z ^ (k.val + 1)‖ ≤ (1 + ε) * Real.sqrt ↑n :=
  sorry

end
