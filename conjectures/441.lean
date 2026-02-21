import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Group.Even

open Finset Filter

/-!
# Erdős Problem #441

Let $N \geq 1$. What is the size of the largest $A \subseteq \{1, \ldots, N\}$
such that $\text{lcm}(a, b) \leq N$ for all $a, b \in A$?

Is it attained by choosing all integers in $[1, (N/2)^{1/2}]$ together with
all even integers in $[(N/2)^{1/2}, (2N)^{1/2}]$?

This construction gives $g(N) \geq (9N/8)^{1/2} + O(1)$. Erdős [Er51b] proved
$g(N) \leq (4N)^{1/2} + O(1)$. Chen [Ch98] established the asymptotic
$g(N) \sim (9N/8)^{1/2}$. Chen and Dai [ChDa07] proved that, infinitely often,
Erdős' construction is not optimal, disproving the conjecture.
-/

/-- A finite set A ⊆ {1, …, N} has all pairwise lcm bounded by N. -/
def LcmBounded (A : Finset ℕ) (N : ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

/-- Erdős' construction: all integers in [1, √(N/2)] together with all
even integers in (√(N/2), √(2N)]. -/
noncomputable def erdosConstruction (N : ℕ) : Finset ℕ :=
  let lo := Nat.sqrt (N / 2)
  let hi := Nat.sqrt (2 * N)
  (Finset.Icc 1 lo) ∪ ((Finset.Ioc lo hi).filter (fun m => Even m))

/-- Erdős Problem #441, asymptotic upper bound (PROVED by Chen [Ch98]):
g(N) ~ (9N/8)^{1/2}. For any ε > 0 and sufficiently large N, any
A ⊆ {1, …, N} with all pairwise lcm ≤ N satisfies |A| ≤ (1+ε)·√(9N/8). -/
theorem erdos_problem_441_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, LcmBounded A N →
    (A.card : ℝ) ≤ (1 + ε) * Real.sqrt (9 * N / 8) :=
  sorry

/-- Erdős Problem #441, asymptotic lower bound (PROVED by construction):
For any ε > 0 and sufficiently large N, there exists A ⊆ {1, …, N} with
all pairwise lcm ≤ N and |A| ≥ (1-ε)·√(9N/8). -/
theorem erdos_problem_441_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ, LcmBounded A N ∧
    (1 - ε) * Real.sqrt (9 * N / 8) ≤ (A.card : ℝ) :=
  sorry

/-- Erdős Problem #441, original conjecture (DISPROVED by Chen–Dai [ChDa07]):
It is NOT true that Erdős' construction is optimal for all N. For infinitely
many N, there exists A with |A| > |erdosConstruction N| and all pairwise
lcm ≤ N. -/
theorem erdos_problem_441_disproved :
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    ∃ A : Finset ℕ, LcmBounded A N ∧
    (erdosConstruction N).card < A.card :=
  sorry
