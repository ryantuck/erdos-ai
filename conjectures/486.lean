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
Erdős Problem #486 [Er61,p.235]:

Let A ⊆ ℕ, and for each n ∈ A choose some Xₙ ⊆ ℤ/nℤ. Let
  B = { m ∈ ℕ : m ∉ Xₙ (mod n) for all n ∈ A with m > n }.
Must B have a logarithmic density?

This is a generalisation of problem #25, which is the case |Xₙ| = 1 for all n.
-/
theorem erdos_problem_486
    (A : Set ℕ)
    (X : (n : ℕ) → Set (ZMod n))
    (B : Set ℕ := {m : ℕ | ∀ n ∈ A, m > n →
      (m : ZMod n) ∉ X n}) :
    ∃ d : ℝ, logDensity B d :=
  sorry
