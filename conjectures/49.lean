import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/--
Erdős Problem #49:

Let A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N} be such that φ(a₁) < ⋯ < φ(aₜ),
i.e., the Euler totient function is strictly increasing on A (in the
ordering inherited from ℕ). The primes are such an example.

The conjecture (now proved by Tao) is that |A| ≤ (1 + o(1))π(N), i.e.,
for every ε > 0, for all sufficiently large N, any such A satisfies
|A| ≤ (1 + ε) · π(N).
-/
theorem erdos_problem_49 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) :=
  sorry
