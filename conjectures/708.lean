import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Nat Finset BigOperators

noncomputable section

/-!
# Erdős Problem #708

Let g(n) be minimal such that for any A ⊆ [2,∞) ∩ ℕ with |A| = n and any set I
of max(A) consecutive integers there exists some B ⊆ I with |B| = g(n) such that
∏_{a ∈ A} a ∣ ∏_{b ∈ B} b.

Is it true that g(n) ≤ (2+o(1))n? Or perhaps even g(n) ≤ 2n?

A problem of Erdős and Surányi [ErSu59], who proved that g(n) ≥ (2-o(1))n,
and that g(3) = 4. Gallai first considered such problems and observed g(2) = 2.

https://www.erdosproblems.com/708
-/

/--
Erdős Problem #708 (weak form): g(n) ≤ (2+o(1))n.

For every ε > 0, there exists N₀ such that for all nonempty A ⊆ {2, 3, ...}
with |A| ≥ N₀ and every interval of max(A) consecutive natural numbers starting
at k, there exists a subset B of that interval with |B| ≤ (2+ε)|A| whose product
is divisible by the product of A.
-/
theorem erdos_problem_708_weak :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ (A : Finset ℕ) (hA : A.Nonempty),
    N₀ ≤ A.card → (∀ a ∈ A, 2 ≤ a) →
    ∀ (k : ℕ),
    ∃ B : Finset ℕ, B ⊆ Finset.Icc k (k + A.max' hA - 1) ∧
      (B.card : ℝ) ≤ (2 + ε) * A.card ∧
      (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) :=
  sorry

/--
Erdős Problem #708 (strong form): g(n) ≤ 2n.

For every nonempty finite set A ⊆ {2, 3, ...} and every interval of max(A)
consecutive natural numbers starting at k, there exists a subset B of that
interval with |B| ≤ 2|A| whose product is divisible by the product of A.
-/
theorem erdos_problem_708_strong :
    ∀ (A : Finset ℕ) (hA : A.Nonempty), (∀ a ∈ A, 2 ≤ a) →
    ∀ (k : ℕ),
    ∃ B : Finset ℕ, B ⊆ Finset.Icc k (k + A.max' hA - 1) ∧
      B.card ≤ 2 * A.card ∧
      (∏ a ∈ A, a) ∣ (∏ b ∈ B, b) :=
  sorry

end
