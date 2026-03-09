import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Nat Finset

noncomputable section

/--
A finset S of natural numbers is **pairwise coprime** if every two distinct
elements of S have gcd equal to 1.
-/
def PairwiseCoprime (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/--
The set A has no k+1 pairwise coprime elements: there is no subset of A
of size k+1 whose elements are pairwise coprime.
-/
def NoPairwiseCoprimeSubset (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = k + 1 → ¬PairwiseCoprime S

/--
The set of all multiples of the first k primes in {1,…,N}: that is,
{m ∈ {1,…,N} | ∃ i < k, (the i-th prime) divides m}.
-/
def multiplesOfFirstKPrimes (N k : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun m =>
    ∃ i : ℕ, i < k ∧ (nth Nat.Prime i) ∣ (m + 1)

/--
Erdős Problem #56 [Er65, Er73, Er92b, Er92c, Er95]:

Let N ≥ p_k where p_k is the k-th prime. Suppose A ⊆ {1,…,N} is such that
there are no k+1 elements of A which are pairwise coprime. An example is
the set of all multiples of the first k primes. Is this the largest such set?

This was **disproved** for k = 212 by Ahlswede and Khachatrian [AhKh94].
Erdős later asked whether the conjecture holds for N sufficiently large
depending on k, which was proved by Ahlswede and Khachatrian [AhKh95].
-/
theorem erdos_problem_56 :
    ∀ (N k : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      nth Nat.Prime (k - 1) ≤ N →
      NoPairwiseCoprimeSubset A k →
      A.card ≤ (multiplesOfFirstKPrimes N k).card :=
  sorry
