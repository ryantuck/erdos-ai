import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
Erdős Problem #672 [Er97c, Va99]:

Can the product of an arithmetic progression of positive integers
n, n+d, …, n+(k-1)d of length k ≥ 4 (with gcd(n,d) = 1) be a perfect power?

Erdős believed not. Erdős and Selfridge proved that the product of consecutive
integers is never a perfect power. Györy, Hajdu, and Pintér proved this is
impossible for 4 ≤ k ≤ 34.
-/
theorem erdos_problem_672 :
    ∀ (n d k : ℕ),
      0 < n → 0 < d → 4 ≤ k →
      Nat.Coprime n d →
      ¬ ∃ (a m : ℕ), 2 ≤ m ∧
        (Finset.range k).prod (fun i => n + i * d) = a ^ m :=
  sorry
