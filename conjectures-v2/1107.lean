import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset Classical

noncomputable section

/-!
# Erdős Problem #1107

Let r ≥ 2. A number n is r-powerful if for every prime p which divides n
we have p^r ∣ n. Is every large integer the sum of at most r+1 many
r-powerful numbers?

Given in the 1986 Oberwolfach problem book as a problem of Erdős and Ivić
[Ob1]. The problem's status is OPEN; the case r = 2 is settled:

This is true when r = 2, as proved by Heath-Brown [He88] (see problem #941):
every sufficiently large integer is the sum of at most three 2-powerful
(i.e. squarefull) numbers.

See problem #940 for the problem of which integers are the sum of at most
r many r-powerful numbers.

## References

Bibliographic details below are honest stubs recovered from the archived
problem page and sibling files in this repo (the [He88] entry is carried by
problem #941's file); no /latex/1107 capture exists, so full verification
awaits network access to erdosproblems.com/latex/1107.

- [Ob1] Oberwolfach problem session (1986).
- [He88] Heath-Brown, D.R., _Ternary quadratic forms and sums of three
  square-full numbers_. Séminaire de Théorie des Nombres, Paris 1986–87
  (1988), 137–163.

https://www.erdosproblems.com/1107
Tags: number theory, powerful
Related OEIS sequences: A056828, A392342, A392343
-/

/-- A positive natural number n is **r-powerful** if for every prime p dividing n,
we have p^r ∣ n. (In particular 1 is r-powerful, vacuously; the positivity
conjunct excludes 0, matching the standard convention for powerful numbers.) -/
def IsRPowerful1107 (r : ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/-- A natural number m is expressible as the sum of at most k many r-powerful numbers. -/
def IsSumOfAtMostRPowerful1107 (r : ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ (j : ℕ) (f : Fin j → ℕ), j ≤ k ∧
    (∀ i, IsRPowerful1107 r (f i)) ∧
    m = ∑ i, f i

/--
Erdős Problem #1107 [Ob1]:

Let r ≥ 2. Is every sufficiently large integer the sum of at most r+1 many
r-powerful numbers?

That is, for each r ≥ 2 there exists N₀ such that for all n ≥ N₀, n can be
written as a sum of at most r+1 many r-powerful numbers.

This question is OPEN in general; the statement below asserts the
conjectured affirmative direction, following this corpus's convention for
open yes/no questions. The case r = 2 is a theorem of Heath-Brown [He88]
(see `erdos_problem_1107_heath_brown` below and problem #941).
-/
theorem erdos_problem_1107 (r : ℕ) (hr : 2 ≤ r) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      IsSumOfAtMostRPowerful1107 r (r + 1) n :=
  sorry

/--
Variant (Heath-Brown [He88]): the case r = 2 of Erdős Problem #1107.

Every sufficiently large integer is the sum of at most three 2-powerful
(i.e. squarefull) numbers. This is the solved case recorded on the problem
page ("This is true when r = 2, as proved by Heath-Brown"); see also
problem #941, which states the same theorem.
-/
theorem erdos_problem_1107_heath_brown :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      IsSumOfAtMostRPowerful1107 2 3 n :=
  sorry

end
