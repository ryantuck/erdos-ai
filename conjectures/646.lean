import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem #646

Let p_1, ..., p_k be distinct primes. Are there infinitely many n such that
n! is divisible by an even power of each of the p_i?

The answer is yes, proved by Berend [Be97], who further proved that the
sequence of such n has bounded gaps (where the bound depends on the initial
set of primes).
-/

/--
Erdős Problem #646 (proved by Berend [Be97]):

For any finite set of primes, there are infinitely many n such that
n! is divisible by an even power of each prime in the set. Equivalently,
for each prime p in the set, the p-adic valuation of n! is even.
-/
theorem erdos_problem_646
    (primes : Finset ℕ)
    (hprimes : ∀ p ∈ primes, Nat.Prime p) :
    Set.Infinite {n : ℕ | ∀ p ∈ primes, Even (padicValNat p n.factorial)} :=
  sorry
