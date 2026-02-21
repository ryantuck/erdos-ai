import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-- The product of `k` consecutive natural numbers starting from `m + 1`:
    (m+1)(m+2)⋯(m+k). -/
def consecutiveProduct388 (m k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (m + 1 + i)

/-!
# Erdős Problem #388

Can one classify all solutions of
  ∏_{1 ≤ i ≤ k₁} (m₁ + i) = ∏_{1 ≤ j ≤ k₂} (m₂ + j)
where k₁, k₂ > 3 and m₁ + k₁ ≤ m₂? Are there only finitely many solutions?

More generally, if k₁ > 2 then for fixed a and b,
  a · ∏_{1 ≤ i ≤ k₁} (m₁ + i) = b · ∏_{1 ≤ j ≤ k₂} (m₂ + j)
should have only a finite number of solutions.

See also problems [363] and [931].
-/

/--
Erdős Problem #388 [Er76d] [ErGr80] [Er92e]:

There are only finitely many 4-tuples (m₁, k₁, m₂, k₂) of natural numbers
with k₁, k₂ > 3 and m₁ + k₁ ≤ m₂ such that
  (m₁+1)(m₁+2)⋯(m₁+k₁) = (m₂+1)(m₂+2)⋯(m₂+k₂).
-/
theorem erdos_problem_388 :
    Set.Finite {t : ℕ × ℕ × ℕ × ℕ |
      3 < t.2.1 ∧ 3 < t.2.2.2 ∧
      t.1 + t.2.1 ≤ t.2.2.1 ∧
      consecutiveProduct388 t.1 t.2.1 = consecutiveProduct388 t.2.2.1 t.2.2.2} :=
  sorry
