import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

/-!
# Erdős Problem #1059

Are there infinitely many primes $p$ such that $p - k!$ is composite for each
$k$ such that $1 \leq k! < p$?

A question of Erdős reported in problem A2 of Guy's collection [Gu04].
Examples are $p = 101$ and $p = 211$.

https://www.erdosproblems.com/1059
-/

/--
Erdős Problem #1059:

Are there infinitely many primes `p` such that `p - k!` is composite for
every `k` with `1 ≤ k!` and `k! < p`?

Equivalently, the set of primes `p` such that for every factorial `d` with
`1 ≤ d < p`, the difference `p - d` is composite, is infinite.
-/
theorem erdos_problem_1059 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      ∀ k : ℕ, 1 ≤ k.factorial → k.factorial < p →
        ¬ Nat.Prime (p - k.factorial)} :=
  sorry
