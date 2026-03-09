import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Card

open BigOperators Finset

/--
An integer `m` is representable by a finite set `A ⊆ ℕ` if it can be written
as a nonnegative integer linear combination of elements of `A`, i.e.,
`m = ∑ a ∈ A, a * f(a)` for some `f : ℕ → ℕ`.
-/
def IsRepresentable (A : Finset ℕ) (m : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, m = ∑ a ∈ A, a * f a

/--
The set of positive integers not representable by `A`.
-/
def NonRepresentableSet (A : Finset ℕ) : Set ℕ :=
  {m : ℕ | 0 < m ∧ ¬ IsRepresentable A m}

/--
Erdős Problem #434 [ErGr80, p.86]:

Let k ≤ n with k ≥ 2. Among all A ⊆ {1,…,n} with gcd(A) = 1 and |A| = k,
the set {n−k+1, n−k+2, …, n} maximises the number of positive integers
not representable as a nonnegative integer linear combination of elements of A.

Associated with problems of Frobenius (see also [433]).
Proved by Kiss (2002).
-/
theorem erdos_problem_434
    (k n : ℕ) (hkn : k ≤ n) (hk : 2 ≤ k)
    (A : Finset ℕ)
    (hA_sub : ∀ a ∈ A, 1 ≤ a ∧ a ≤ n)
    (hA_card : A.card = k)
    (hA_gcd : A.gcd id = 1) :
    Set.ncard (NonRepresentableSet A) ≤
      Set.ncard (NonRepresentableSet (Finset.Icc (n - k + 1) n)) :=
  sorry
