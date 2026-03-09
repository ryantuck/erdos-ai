import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat Finset

namespace Erdos1093

/--
A natural number `m` is `k`-smooth if all of its prime factors are at most `k`.
-/
def IsSmooth (k m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ≤ k

open Classical in
/--
Whether the deficiency of `C(n, k)` is defined: it is defined when `n ≥ 2k`
and `C(n, k)` is not divisible by any prime `p ≤ k`.
-/
def deficiencyDefined (n k : ℕ) : Prop :=
  2 * k ≤ n ∧ ∀ p : ℕ, p.Prime → p ≤ k → ¬(p ∣ Nat.choose n k)

open Classical in
/--
The deficiency of `C(n, k)` (when defined) is the number of `0 ≤ i < k` such that
`n - i` is `k`-smooth.
-/
noncomputable def deficiency (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => IsSmooth k (n - i))).card

/--
Erdős Problem #1093, Part 1 (OPEN) [ELS88,p.522]:

A problem of Erdős, Lacampagne, and Selfridge. For n ≥ 2k, define the deficiency
of C(n,k) as the number of 0 ≤ i < k such that n - i is k-smooth, provided that
C(n,k) is not divisible by any prime p ≤ k.

Are there infinitely many binomial coefficients with deficiency 1?
-/
theorem erdos_problem_1093_part1 :
    Set.Infinite {p : ℕ × ℕ | deficiencyDefined p.1 p.2 ∧ deficiency p.1 p.2 = 1} :=
  sorry

/--
Erdős Problem #1093, Part 2 (OPEN) [ELS88,p.522]:

Are there only finitely many binomial coefficients with deficiency > 1?
-/
theorem erdos_problem_1093_part2 :
    Set.Finite {p : ℕ × ℕ | deficiencyDefined p.1 p.2 ∧ deficiency p.1 p.2 > 1} :=
  sorry

end Erdos1093
