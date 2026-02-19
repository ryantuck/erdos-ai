import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset BigOperators

/--
A number `m` is practical if every integer `1 ≤ n < m` is the sum of distinct divisors of `m`.
-/
def IsPractical (m : ℕ) : Prop :=
  ∀ n, 1 ≤ n ∧ n < m → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ x ∈ s, x = n

/--
For a practical number `m`, `h(m)` is the maximum over `1 ≤ n < m` of the minimum number
of distinct divisors of `m` needed to sum to `n`.
If `m` is not practical or `m = 1`, this definition returns 0.
-/
noncomputable def h (m : ℕ) : ℕ :=
  let range_max := (Ico 1 m).image (fun n =>
    let subsets := m.divisors.powerset.filter (fun s => ∑ x ∈ s, x = n)
    (subsets.image card).toList.minimum.getD 0
  )
  range_max.toList.maximum.getD 0

/--
The main conjecture from Erdős Problem #18:
Is it true that h(n!) < (log n)^O(1)?
Formalized as: There exist constants C and k such that for all n ≥ 2, h(n!) ≤ C * (log n)^k.
-/
theorem erdos_problem_18_conjecture :
  ∃ (C k : ℝ), ∀ n, 2 ≤ n → (h (n !) : ℝ) ≤ C * (Real.log (n : ℝ)) ^ k :=
sorry

/--
Another variation mentioned:
Are there infinitely many practical m such that h(m) < (log log m)^O(1)?
-/
theorem erdos_problem_18_conjecture_practical_infinite :
  ∃ (C k : ℝ), Set.Infinite {m : ℕ | IsPractical m ∧ (h m : ℝ) ≤ C * (Real.log (Real.log (m : ℝ))) ^ k} :=
sorry
