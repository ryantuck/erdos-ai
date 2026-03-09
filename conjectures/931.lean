import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/--
The product of consecutive integers (n+1)(n+2)⋯(n+k).
-/
noncomputable def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i + 1)

/--
Erdős Problem #931 [Er76d]:

Let k₁ ≥ k₂ ≥ 3. Are there only finitely many pairs (n₁, n₂) with
n₂ ≥ n₁ + k₁ such that ∏_{i=1}^{k₁} (n₁ + i) and ∏_{j=1}^{k₂} (n₂ + j)
have the same set of prime factors?

Tijdeman gave the example 19·20·21·22 and 54·55·56·57 (with k₁ = k₂ = 4).
-/
theorem erdos_problem_931 :
    ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
      Set.Finite {p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
        (consecutiveProduct p.1 k₁).primeFactors =
        (consecutiveProduct p.2 k₂).primeFactors} :=
  sorry
