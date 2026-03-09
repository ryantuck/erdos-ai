import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

open Nat Finset Classical

noncomputable section

/--
A positive natural number n is **r-powerful** if for every prime p dividing n,
we have p^r ∣ n.
-/
def IsRPowerful (r : ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/--
A natural number m is expressible as the sum of at most r many r-powerful numbers.
-/
def IsSumOfRPowerful (r : ℕ) (m : ℕ) : Prop :=
  ∃ (k : ℕ) (f : Fin k → ℕ), k ≤ r ∧
    (∀ i, IsRPowerful r (f i)) ∧
    m = ∑ i, f i

/--
Erdős Problem #940 [Er76d, Ob1]:

Let r ≥ 3. A number n is r-powerful if for every prime p dividing n we have
p^r ∣ n.

Part (a): Are there infinitely many integers which are not the sum of at most
r many r-powerful numbers?

Part (b): Does the set of integers which are the sum of at most r many
r-powerful numbers have density 0?

Erdős and Ivić conjectured both parts. For r = 2 the density-0 claim was
proved by Baker and Brüdern (1994). For r = 3 it is not even known whether
the set of sums of at most three cubes has density 0.
-/
theorem erdos_problem_940a (r : ℕ) (hr : 3 ≤ r) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ¬ IsSumOfRPowerful r n :=
  sorry

theorem erdos_problem_940b (r : ℕ) (hr : 3 ≤ r) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ((Finset.range N).filter (fun n => IsSumOfRPowerful r n)).card < ε * (N : ℝ) :=
  sorry
