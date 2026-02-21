import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

open scoped Classical
open Finset BigOperators

/-- The signed sum of complex numbers z with signs ε ∈ {-1, 1}ⁿ (encoded as Bool). -/
noncomputable def signedSum498 {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i : Fin n, (if ε i then (1 : ℂ) else (-1 : ℂ)) * z i

/--
Erdős Problem #498 (Littlewood-Offord problem, proved by Kleitman [Kl65]):

Let z₁, ..., zₙ ∈ ℂ with |zᵢ| ≥ 1 for all i. For any disc of radius 1
centered at w ∈ ℂ, the number of sign patterns ε ∈ {-1, 1}ⁿ such that
ε₁z₁ + ⋯ + εₙzₙ lies in the disc (i.e., ‖∑ εᵢzᵢ - w‖ ≤ 1) is at most
C(n, ⌊n/2⌋).

This is a strong form of the Littlewood-Offord problem. Erdős [Er45] proved
the real case. Kleitman [Kl65] proved the full complex case and later
generalised the result to arbitrary Hilbert spaces [Kl70].
-/
theorem erdos_problem_498 (n : ℕ) (z : Fin n → ℂ) (w : ℂ)
    (hz : ∀ i, 1 ≤ ‖z i‖) :
    (Finset.univ.filter (fun ε : Fin n → Bool =>
      ‖signedSum498 z ε - w‖ ≤ 1)).card ≤ n.choose (n / 2) :=
  sorry
