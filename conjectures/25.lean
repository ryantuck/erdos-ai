import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Order.Filter.Basic

open Filter Set Classical

noncomputable section

/--
The logarithmic density of a set A ⊆ ℕ⁺ is defined as
  δ(A) = lim_{N→∞} (1 / log N) · ∑_{n ∈ A, 1 ≤ n ≤ N} 1/n,
when this limit exists.
-/
def logDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ =>
    (Real.log N)⁻¹ * ∑ n ∈ Finset.Icc 1 N, if n ∈ A then (n : ℝ)⁻¹ else 0)
    atTop (nhds d)

/--
Erdős Problem #25 [Er95]:

Let 1 ≤ n₁ < n₂ < ⋯ be an arbitrary sequence of integers, each with an
associated residue class aᵢ (mod nᵢ). Let A be the set of integers n such
that for every i either n < nᵢ or n ≢ aᵢ (mod nᵢ). Must the logarithmic
density of A exist?

This is a special case of problem #486.
-/
theorem erdos_problem_25
    (moduli : ℕ → ℕ)
    (hmod_pos : ∀ i, 1 ≤ moduli i)
    (hmod_strict_mono : StrictMono moduli)
    (residues : ℕ → ℤ)
    (A : Set ℕ := {n : ℕ | ∀ i, n < moduli i ∨ ¬((n : ℤ) ≡ residues i [ZMOD (moduli i : ℤ)])}) :
    ∃ d : ℝ, logDensity A d :=
  sorry
