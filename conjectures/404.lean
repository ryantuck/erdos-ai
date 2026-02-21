import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators Filter

/-!
# Erdős Problem #404

For which integers a ≥ 1 and primes p is there a finite upper bound on those k
such that there are a = a₁ < ⋯ < aₙ with p^k ∣ (a₁! + ⋯ + aₙ!)? If f(a,p)
is the greatest such k, how does this function behave?

Is there a prime p and an infinite sequence a₁ < a₂ < ⋯ such that if p^{mₖ}
is the highest power of p dividing ∑_{i ≤ k} aᵢ! then mₖ → ∞?

See also [403]. Lin [Li76] has shown that f(2,2) ≤ 254.
-/

/--
Erdős Problem #404, Part 1 [ErGr80, p.79]:

For all integers a ≥ 1 and all primes p, there is a finite upper bound on the
p-adic valuation of sums a₁! + ⋯ + aₙ! over all finite sets {a₁, …, aₙ} with
a as the minimum element.

Formally: for every a ≥ 1 and every prime p, there exists K such that for every
finite set S of natural numbers with a ∈ S and a ≤ x for all x ∈ S, we have
padicValNat p (∑ i in S, i!) ≤ K.
-/
theorem erdos_problem_404_part1 (a : ℕ) (ha : 1 ≤ a) (p : ℕ) (hp : Nat.Prime p) :
    ∃ K : ℕ, ∀ S : Finset ℕ, a ∈ S → (∀ x ∈ S, a ≤ x) →
      padicValNat p (∑ i ∈ S, i.factorial) ≤ K :=
  sorry

/--
Erdős Problem #404, Part 2 [ErGr80, p.79]:

There is no prime p and strictly increasing sequence a₁ < a₂ < ⋯ of natural
numbers such that the p-adic valuation of the partial sums ∑_{i ≤ k} aᵢ! tends
to infinity.

This is a consequence of Part 1: if f(a,p) is always finite, then for any
sequence starting at a₁, the p-adic valuation of partial sums is bounded by
f(a₁, p).
-/
theorem erdos_problem_404_part2 :
    ¬∃ (p : ℕ) (_ : Nat.Prime p) (a : ℕ → ℕ), StrictMono a ∧
      Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k + 1), (a i).factorial))
        atTop atTop :=
  sorry
