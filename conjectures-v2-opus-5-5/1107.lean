-- [AI-Generated]: Erdős Problem 1107 — second-pass formalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset Classical

noncomputable section

/-!
# Erdős Problem #1107

*Source:* [erdosproblems.com/1107](https://www.erdosproblems.com/1107) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
18 November 2025, captured 2026-03-09). [Ob1]

Let r ≥ 2. A number n is r-powerful if for every prime p which divides n
we have p^r ∣ n. Is every large integer the sum of at most r+1 many
r-powerful numbers?

Given in the 1986 Oberwolfach problem book as a problem of Erdős and Ivić [Ob1].
This is true when r = 2, as proved by Heath-Brown [He88] (see problem #941). See problem
#940 for the problem of which integers are the sum of at most r many r-powerful numbers.

Computation (review scratch script, 1 counted as r-powerful, repetitions allowed). Up to
2 · 10⁵, the integers that are not sums of at most r + 1 r-powerful numbers are:
* r = 2: exactly 7, 15, 23, 87, 111, 119;
* r = 3: 45 integers, the largest being 2039;
* r = 4: 1318 integers, with the largest found 150271, so the threshold for r = 4 lies
  beyond this range.
This is consistent with the conjecture, but no finite computation can settle it.

Tags: number theory, powerful. OEIS: A056828, A392342, A392343 (and "possible"). The page
records an upstream formalised statement.

## References

* [Ob1] P. Erdős, _Oberwolfach Mathematical Problems, Volume 1_. Mathematisches
  Forschungsinstitut Oberwolfach (problem posed 1986).
* [He88] Heath-Brown, D. R., _Ternary quadratic forms and sums of three square-full
  numbers_. (1988), 137–163.

(Provenance: the original pipeline's fetches of `erdosproblems.com/latex/854` for [Ob1] and
`/latex/941` for [He88], both citing the same keys. Proceedings and volume data are not in
those extractions.)
-/

/-- A positive natural number n is **r-powerful** if for every prime p dividing n,
we have p^r ∣ n. (So 1 is r-powerful, and 0 is excluded.) -/
def IsRPowerful1107 (r : ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/-- A natural number m is expressible as the sum of at most k many r-powerful numbers
(repetitions allowed). -/
def IsSumOfAtMostRPowerful1107 (r : ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ (j : ℕ) (f : Fin j → ℕ), j ≤ k ∧
    (∀ i, IsRPowerful1107 r (f i)) ∧
    m = ∑ i, f i

/--
Erdős Problem #1107 [Ob1] (OPEN):

Let r ≥ 2. Is every sufficiently large integer the sum of at most r+1 many
r-powerful numbers?

That is, for each r ≥ 2 there exists N₀ such that for all n ≥ N₀, n can be
written as a sum of at most r+1 many r-powerful numbers.

Stated in the asked ("yes") direction as a direct assertion (this raw corpus has no
`answer()` elaborator); the case r = 2 is Heath-Brown's theorem,
`erdos_problem_1107.variants.heath_brown`.
-/
theorem erdos_problem_1107 (r : ℕ) (hr : 2 ≤ r) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      IsSumOfAtMostRPowerful1107 r (r + 1) n :=
  sorry

/-- Heath-Brown [He88] (solved; problem #941): every sufficiently large integer is the
sum of at most three powerful (2-powerful) numbers. (By computation the exceptions up to
2 · 10⁵ are 7, 15, 23, 87, 111, 119.) -/
theorem erdos_problem_1107.variants.heath_brown :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      IsSumOfAtMostRPowerful1107 2 3 n :=
  sorry

end
