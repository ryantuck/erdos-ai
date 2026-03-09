import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
An integer m ≥ 2 is a **primary pseudoperfect number** if there exist distinct
primes p₁, …, pₖ such that 1/p₁ + ⋯ + 1/pₖ = 1 - 1/m.
-/
def IsPrimaryPseudoperfect (m : ℕ) : Prop :=
  ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧
    ∑ p ∈ P, (1 : ℚ) / (p : ℚ) = 1 - 1 / (m : ℚ)

/--
Erdős Problem #313 [ErGr80, p.40]:

Are there infinitely many solutions to
  1/p₁ + ⋯ + 1/pₖ = 1 - 1/m,
where m ≥ 2 is an integer and p₁ < ⋯ < pₖ are distinct primes?

Such m are called primary pseudoperfect numbers. It is known that m = p₁⋯pₖ,
so there is at most one solution for each m. There are 8 known examples
(OEIS A054377): 2, 6, 42, 1806, 47058, 2214502422, …
-/
theorem erdos_problem_313 :
    Set.Infinite {m : ℕ | 2 ≤ m ∧ IsPrimaryPseudoperfect m} :=
  sorry
