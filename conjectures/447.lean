import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #447

How large can a union-free collection F of subsets of [n] be? By union-free
we mean there are no solutions to A ∪ B = C with distinct A, B, C ∈ F.

Erdős conjectured that |F| < (1 + o(1)) * C(n, ⌊n/2⌋).

Solved by Kleitman [Kl71], who proved the conjectured bound.
-/

/-- A family of finsets is union-free if there are no three distinct members
    A, B, C with A ∪ B = C. -/
def UnionFreeFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- Erdős Problem #447 (Kleitman's Theorem [Kl71]):
For every ε > 0, there exists N₀ such that for all n ≥ N₀, if F is a
union-free family of subsets of Fin n, then |F| ≤ (1 + ε) * C(n, ⌊n/2⌋). -/
theorem erdos_problem_447 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ F : Finset (Finset (Fin n)),
    UnionFreeFamily F →
    (F.card : ℝ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℝ) :=
  sorry
