import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #879

Call a set S ⊆ {1, …, n} *admissible* if gcd(a,b) = 1 for all distinct a, b ∈ S.
Let G(n) = max { ∑ a∈S a : S admissible, S ⊆ {1,…,n} } and
    H(n) = ∑_{p < n} p + n · π(√n).

Is it true that G(n) > H(n) - n^{1+o(1)}?

Is it true that, for every k ≥ 2, if n is sufficiently large then the admissible
set which maximises G(n) contains at least one integer with at least k prime factors?
-/

/-- A finset of natural numbers is admissible (pairwise coprime) if every two
    distinct elements are coprime. -/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/-- An admissible subset of {1, …, n} that achieves the maximum sum among all
    admissible subsets of {1, …, n}. -/
def IsMaxAdmissible (S : Finset ℕ) (n : ℕ) : Prop :=
  S ⊆ Finset.Icc 1 n ∧ IsAdmissible S ∧
  ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 n → IsAdmissible T → T.sum id ≤ S.sum id

/-- H(n) = (sum of primes less than n) + n · π(√n). -/
noncomputable def H (n : ℕ) : ℕ :=
  ((Finset.range n).filter Nat.Prime).sum id +
  n * ((Finset.range (Nat.sqrt n + 1)).filter Nat.Prime).card

/--
Erdős Problem #879, Part 1:

For every ε > 0, for all sufficiently large n, G(n) > H(n) - n^{1+ε}.
-/
theorem erdos_problem_879_part1 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ, IsMaxAdmissible S n →
    (↑(S.sum id) : ℝ) > (↑(H n) : ℝ) - (↑n : ℝ) ^ ((1 : ℝ) + ε) :=
  sorry

/--
Erdős Problem #879, Part 2:

For every k ≥ 2, if n is sufficiently large then any admissible set maximising
G(n) contains at least one integer with at least k distinct prime factors.
-/
theorem erdos_problem_879_part2 :
    ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ, IsMaxAdmissible S n →
    ∃ a ∈ S, a.primeFactors.card ≥ k :=
  sorry

end
