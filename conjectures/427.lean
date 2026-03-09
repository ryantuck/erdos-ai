import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset BigOperators

/--
Erdős Problem #427 [ErGr80]:

Is it true that, for every n and d, there exists k such that
  d ∣ p_{n+1} + p_{n+2} + ⋯ + p_{n+k},
where pᵣ denotes the r-th prime?

This has been proved. Cedric Pilatte observed that a positive solution
follows from a result of Shiu (2000): for any l ≥ 1 and (a, q) = 1
there exist infinitely many l-tuples of consecutive primes all
congruent to a modulo q.

Using 0-indexed `Nat.nth Nat.Prime`, the r-th prime (1-indexed) is
`Nat.nth Nat.Prime (r - 1)`. The sum p_{n+1} + ⋯ + p_{n+k} becomes
∑ i ∈ Finset.range k, Nat.nth Nat.Prime (n + i).
-/
theorem erdos_problem_427
    (n d : ℕ) (hd : 0 < d) :
    ∃ k : ℕ, 0 < k ∧
      d ∣ ∑ i ∈ Finset.range k, Nat.nth Nat.Prime (n + i) :=
  sorry
