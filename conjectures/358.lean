import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Card

open BigOperators Finset Filter

/--
The set of pairs (u, v) with u ≤ v such that ∑_{i=u}^{v} A(i) = n.
These represent ways to write n as a sum of consecutive terms of A.
-/
def consecutiveSumReps (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | p.1 ≤ p.2 ∧ ∑ i ∈ Icc p.1 p.2, A i = n}

/--
f(n) counts the number of representations of n as a sum of consecutive terms of A.
-/
noncomputable def consecutiveSumCount (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (consecutiveSumReps A n)

/--
Erdős Problem #358 [Er77c, ErGr80]:

Let A = {a₁ < a₂ < ⋯} be an infinite strictly increasing sequence of positive
integers. Let f(n) count the number of ways to write n = ∑_{u ≤ i ≤ v} aᵢ
as a sum of consecutive terms of A.

Is there such an A for which f(n) → ∞ as n → ∞?

When A = {1, 2, 3, …}, f(n) counts the number of odd divisors of n.
-/
theorem erdos_problem_358_strong :
    ∃ A : ℕ → ℕ, StrictMono A ∧
      Tendsto (consecutiveSumCount A) atTop atTop :=
  sorry

/--
Erdős Problem #358 (weak form):

Is there an infinite strictly increasing sequence A of positive integers
such that f(n) ≥ 2 for all sufficiently large n?
-/
theorem erdos_problem_358_weak :
    ∃ A : ℕ → ℕ, StrictMono A ∧
      ∀ᶠ n in atTop, 2 ≤ consecutiveSumCount A n :=
  sorry
