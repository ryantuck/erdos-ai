import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open Polynomial

/-- For a sequence z : ℕ → ℂ, the product polynomial of the first n roots:
    pₙ(w) = ∏_{i < n} (w − z i). -/
noncomputable def circlePolynomial (z : ℕ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range n, (X - C (z i))

/-- The maximum modulus of circlePolynomial z n on the unit circle:
    Mₙ = max_{|w|=1} |pₙ(w)|. -/
noncomputable def unitCircleMax (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  ⨆ w : {w : ℂ // ‖w‖ = 1}, ‖(circlePolynomial z n).eval w.val‖

/--
Erdős Problem #119 [Er57, Er61, Er64b, Ha74, Er82e, Er90, Er97f, Va99 2.38] — OPEN

Let (zᵢ) be an infinite sequence of complex numbers with |zᵢ| = 1 for all i ≥ 1,
and for n ≥ 1 let
  pₙ(z) = ∏_{i≤n} (z − zᵢ),    Mₙ = max_{|z|=1} |pₙ(z)|.

Three questions were posed:

(1) Is limsup_{n→∞} Mₙ = ∞?
    PROVED: Wagner [Wa80] showed there exists c > 0 such that Mₙ > (log n)^c
    for infinitely many n.

(2) Is there c > 0 such that Mₙ > nᶜ for infinitely many n?
    PROVED: Beck [Be91] showed there exists c > 0 with max_{n≤N} Mₙ > Nᶜ for
    all N. (Erdős gave a construction achieving Mₙ ≤ n+1 for all n; Linden
    [Li77] improved this to Mₙ ≪ n^{1−c} for some c > 0.)

(3) Is there c > 0 such that for all large n, ∑_{k≤n} Mₖ > n^{1+c}?
    This remains OPEN and is the conjecture formalized below.

This is Problem 4.1 in [Ha74], attributed to Erdős.
-/
theorem erdos_problem_119 :
    ∀ (z : ℕ → ℂ), (∀ i, ‖z i‖ = 1) →
    ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (n : ℝ) ^ (1 + c) < ∑ k ∈ Finset.range n, unitCircleMax z k :=
  sorry
