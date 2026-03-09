import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset

noncomputable section

/-!
# Erdős Problem #1108

Let A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }. If k ≥ 2, does A contain only
finitely many k-th powers? Does it contain only finitely many powerful numbers?

Asked by Erdős at Oberwolfach in 1988. It is open even whether there are
infinitely many squares of the form 1 + n! (see problem #398).

https://www.erdosproblems.com/1108
Tags: number theory, factorials
-/

/-- The set A of all sums of distinct factorials: A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }. -/
def IsFactorialSubsetSum1108 (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial

/-- A positive natural number n is **powerful** if for every prime p dividing n,
    we have p² ∣ n. -/
def IsPowerful1108 (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #1108, part 1 [Ob1]:

If k ≥ 2, then A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contains only finitely
many k-th powers.
-/
theorem erdos_problem_1108a (k : ℕ) (hk : 2 ≤ k) :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ ∃ b : ℕ, m = b ^ k} :=
  sorry

/--
Erdős Problem #1108, part 2 [Ob1]:

A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contains only finitely many powerful
numbers.
-/
theorem erdos_problem_1108b :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ IsPowerful1108 m} :=
  sorry

end
