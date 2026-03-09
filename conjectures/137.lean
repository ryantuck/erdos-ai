import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #137

We say that N is powerful if whenever p∣N we also have p²∣N. Let k ≥ 3.
Can the product of any k consecutive positive integers ever be powerful?

Conjectured by Erdős and Selfridge: the answer is NO. Erdős and Selfridge
[ErSe75] proved that the product of k ≥ 3 consecutive positive integers can
never be a perfect power. There are infinitely many n such that n(n+1) is
powerful (see [364]).
-/

/-- A positive natural number N is *powerful* if for every prime p dividing N,
    p² also divides N. -/
def IsPowerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/-- The product of k consecutive positive integers starting at m+1:
    (m+1)(m+2)⋯(m+k). -/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (m + 1 + i)

/--
Erdős Problem #137 (Erdős–Selfridge conjecture) [ErGr80, Er82c, Er97c]:

For all k ≥ 3, the product of k consecutive positive integers is never powerful.
-/
theorem erdos137 :
    ∀ k : ℕ, 3 ≤ k →
      ∀ m : ℕ, ¬ IsPowerful (consecutiveProduct m k) :=
  sorry
