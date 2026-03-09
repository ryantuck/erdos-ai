import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset Classical

noncomputable section

/-- A set of natural numbers is a Sidon set (B₂ set) if all pairwise sums are
    distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have {a,b} = {c,d}. -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The counting function |A ∩ {0, …, N}|. For Sidon sets in ℕ⁺ this equals
    |A ∩ {1, …, N}| since 0 contributes at most one element. -/
noncomputable def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/--
Erdős Problem #329 [Er77c, ErGr80, Er85c]:

Suppose A ⊆ ℕ is a Sidon set. How large can
  limsup_{N → ∞} |A ∩ {1, …, N}| / N^{1/2}
be?

Erdős proved that 1/2 is achievable. Krückeberg [Kr61] proved 1/√2 is
achievable. Erdős and Turán [ErTu41] proved this limsup is always ≤ 1.

The conjecture is that 1 is achievable: there exists an infinite Sidon set
whose counting function grows like √N along a subsequence. This would follow
if every finite Sidon set is a subset of a perfect difference set (see [44]
and [707]).
-/
theorem erdos_problem_329 :
    ∃ A : Set ℕ,
      IsSidonSet A ∧
        ∀ ε : ℝ, 0 < ε →
          ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
            ((countIn A N : ℝ) ≥ (1 - ε) * Real.sqrt (N : ℝ)) :=
  sorry

end
