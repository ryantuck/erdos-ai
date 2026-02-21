import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Fintype.BigOperators

open Finset BigOperators Filter Classical

noncomputable section

/-- Evaluate a ±1-coefficient polynomial of degree n at z ∈ ℂ.
    The sign vector ε : Fin (n+1) → Bool determines coefficients
    (true → +1, false → -1): f(z) = Σ_{k=0}^{n} ε_k · z^k. -/
def littlewoodEval (n : ℕ) (ε : Fin (n + 1) → Bool) (z : ℂ) : ℂ :=
  ∑ k : Fin (n + 1), (if ε k then (1 : ℂ) else (-1 : ℂ)) * z ^ (k : ℕ)

/-- A ±1-coefficient polynomial of degree n has modulus less than 1
    somewhere on the unit circle. -/
def hasSmallValueOnCircle (n : ℕ) (ε : Fin (n + 1) → Bool) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ ‖littlewoodEval n ε z‖ < 1

/-- The number of ±1-coefficient polynomials of degree n that do NOT attain
    modulus less than 1 anywhere on the unit circle. -/
def countNoSmallValue (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun ε : Fin (n + 1) → Bool =>
    ¬hasSmallValueOnCircle n ε)).card

/--
Erdős Problem #525 [Er61, p.253]:

Is it true that all except at most o(2^n) many degree n polynomials with
±1-valued coefficients f(z) have |f(z)| < 1 for some |z| = 1?

Equivalently, the number of sign vectors ε ∈ {±1}^{n+1} for which
the polynomial f(z) = Σ ε_k z^k satisfies min_{|z|=1} |f(z)| ≥ 1
is o(2^n) as n → ∞.

Proved by Kashin (1987). Konyagin (1994) showed
min_{|z|=1} |f(z)| ≤ n^{-1/2+o(1)} for almost all such polynomials.
Cook and Nguyen (2021) identified the limiting distribution.
-/
theorem erdos_problem_525 :
    Tendsto (fun n => (countNoSmallValue n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) :=
  sorry

end
