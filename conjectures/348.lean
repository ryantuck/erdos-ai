import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

open Finset Multiset

/--
A multiset `A` of positive integers is *weakly complete* if every sufficiently large
natural number is a finite subset sum from `A`. That is, there exists a threshold `N`
such that every `n ≥ N` can be expressed as a sum of a finite sub-multiset of `A`.
-/
def WeaklyComplete (A : Multiset ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Multiset ℕ, S ≤ A ∧ S.sum = n

/--
`A` remains weakly complete after removing any `m` elements:
for every sub-multiset `R` of `A` with `Multiset.card R = m`,
the multiset `A - R` is still weakly complete.
-/
def ResilientToRemovals (A : Multiset ℕ) (m : ℕ) : Prop :=
  ∀ R : Multiset ℕ, R ≤ A → Multiset.card R = m → WeaklyComplete (A - R)

/--
Erdős Problem #348 (Erdős–Graham [ErGr80]):
For what values of `0 ≤ m < n` does there exist a weakly complete multiset
`A = {a₁ ≤ a₂ ≤ ⋯}` of positive integers such that:
- `A` remains weakly complete after removing any `m` elements, but
- there exist `n` elements whose removal makes `A` no longer weakly complete?

Known examples:
- `m = 0, n = 1`: the powers of 2 form such a sequence.
- `m = 1, n = 2`: the Fibonacci sequence works.
- `m = 2, n = 3`: open.

The conjecture asserts this holds for all consecutive pairs `m, n = m + 1`.
-/
theorem erdos_problem_348 :
    ∀ m : ℕ,
      ∃ A : Multiset ℕ,
        (∀ a ∈ A, 0 < a) ∧
        WeaklyComplete A ∧
        ResilientToRemovals A m ∧
        ¬ ResilientToRemovals A (m + 1) :=
  sorry
