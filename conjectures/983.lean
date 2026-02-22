import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice

open Classical

noncomputable section

/-!
# Erdős Problem #983

Let n ≥ 2 and π(n) < k ≤ n. Let f(k,n) be the smallest integer r such that
in any A ⊆ {1,...,n} of size |A| = k there exist primes p₁,...,pᵣ such that
more than r elements a ∈ A are only divisible by primes from {p₁,...,pᵣ}.

Is it true that 2π(n^{1/2}) - f(π(n)+1,n) → ∞ as n → ∞?

A problem of Erdős and Straus [Er70b].
-/

/-- The prime counting function π(n): the number of primes ≤ n. -/
def primeCounting (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).card

/-- A natural number a is smooth with respect to a set of primes P if every
    prime factor of a belongs to P. -/
def IsSmoothWrt (a : ℕ) (P : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ a → p ∈ P

/-- f(k,n) is the smallest integer r such that in any A ⊆ {1,...,n} of size k,
    there exist r primes p₁,...,pᵣ such that more than r elements of A are
    only divisible by primes from {p₁,...,pᵣ}. -/
noncomputable def smoothCoveringNumber (k n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → A.card = k →
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.card = r ∧
      ∃ B : Finset ℕ, B ⊆ A ∧ B.card > r ∧ ∀ b ∈ B, IsSmoothWrt b P}

/--
Erdős Problem #983 [Er70b]:

Is it true that 2π(n^{1/2}) - f(π(n)+1, n) → ∞ as n → ∞?

Formulated as: for every M, there exists N₀ such that for all n ≥ N₀,
  f(π(n)+1, n) + M ≤ 2π(⌊√n⌋).
-/
theorem erdos_problem_983 :
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      smoothCoveringNumber (primeCounting n + 1) n + M ≤ 2 * primeCounting (Nat.sqrt n) :=
  sorry

end
