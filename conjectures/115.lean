import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Connected.Basic

open Polynomial

/-- The lemniscate of a complex polynomial p: the sublevel set {z ∈ ℂ : |p(z)| ≤ 1}. -/
def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | Complex.abs (p.eval z) ≤ 1}

/--
Erdős Conjecture (Problem #115) [Er61, Er90], proved by Eremenko–Lempert [ErLe94]:

If p(z) is a polynomial of degree n such that {z ∈ ℂ : |p(z)| ≤ 1} is connected,
then
  max { |p'(z)| : z ∈ ℂ, |p(z)| ≤ 1 } ≤ (1/2 + o(1)) n².

That is, for every ε > 0 there exists N such that for all n ≥ N, every polynomial
p of degree n whose lemniscate is connected satisfies |p'(z)| ≤ (1/2 + ε) n² for
all z in the lemniscate.

The Chebyshev polynomials show that the constant 1/2 is sharp. Erdős originally
conjectured the bound n²/2 exactly (without the o(1)), but Szabados observed that
the stronger form fails. Pommerenke [Po59a] proved the weaker bound (e/2) n².
-/
theorem erdos_problem_115 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.natDegree = n →
      IsConnected (lemniscate p) →
      ∀ z : ℂ, z ∈ lemniscate p →
        Complex.abs ((derivative p).eval z) ≤ (1 / 2 + ε) * (n : ℝ) ^ 2 :=
  sorry
