import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

open Finset Nat

/--
The least common multiple of {1, …, n}, i.e., lcm of all positive integers up to n.
Defined as (Finset.range n).lcm (· + 1) so that we take lcm over {1, …, n}.
When n = 0 this returns 1 (the empty lcm).
-/
def lcmUpTo (n : ℕ) : ℕ := (Finset.range n).lcm (· + 1)

/--
Erdős Problem #458 [ErGr80,p.91]:

Let [1,…,n] denote the least common multiple of {1,…,n}. Is it true that,
for all k ≥ 1,
  [1,…,p_{k+1} - 1] < p_k · [1,…,p_k]?

Here p_k denotes the k-th prime (1-indexed). Using 0-indexed `Nat.nth Nat.Prime`,
p_k (1-indexed) = Nat.nth Nat.Prime (k - 1), so for k ≥ 1 we parametrise by
k : ℕ representing the 0-indexed prime index:
  p_{k+1} = nth Nat.Prime k,  p_{k+2} = nth Nat.Prime (k + 1).

The conjecture becomes: for all k,
  lcm{1,…, nth Nat.Prime (k+1) - 1} < nth Nat.Prime k · lcm{1,…, nth Nat.Prime k}.
-/
theorem erdos_problem_458 :
    ∀ k : ℕ,
      lcmUpTo (nth Nat.Prime (k + 1) - 1) <
        nth Nat.Prime k * lcmUpTo (nth Nat.Prime k) :=
  sorry
