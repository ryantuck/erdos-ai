import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Nat.Lattice

open Finset BigOperators Filter Asymptotics

/-!
# Erdős Problem #433

If A ⊂ ℕ is a finite set with gcd(A) = 1, let G(A) denote the Frobenius number:
the greatest natural number not expressible as a non-negative integer linear
combination of elements of A (with repetitions allowed). Define
  g(k,n) = max G(A)
where the maximum is over all A ⊆ {1,...,n} with |A| = k and gcd(A) = 1.

Is it true that g(k,n) ∼ n²/(k-1)?

This was proved by Dixmier [Di90], who showed that for all 2 ≤ k < n,
  ⌊(n-2)/(k-1)⌋(n-k+1) - 1 ≤ g(k,n) ≤ (⌊(n-1)/(k-1)⌋ - 1)n - 1.
-/

/-- A natural number m is representable by a finite set A if it equals
∑_{a ∈ A} f(a) · a for some coefficient function f : ℕ → ℕ. -/
def Representable433 (A : Finset ℕ) (m : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, ∑ a ∈ A, f a * a = m

/-- The Frobenius number of A: the supremum of natural numbers not representable
as a non-negative integer linear combination of elements of A. Equals 0 when
every natural number is representable (e.g., when 1 ∈ A). -/
noncomputable def FrobeniusNumber433 (A : Finset ℕ) : ℕ :=
  sSup {m : ℕ | ¬ Representable433 A m}

/-- g(k,n) = max G(A) over all A ⊆ {1,...,n} with |A| = k and gcd(A) = 1. -/
noncomputable def g433 (k n : ℕ) : ℕ :=
  sSup (FrobeniusNumber433 '' {A : Finset ℕ | A ⊆ Icc 1 n ∧ A.card = k ∧ A.gcd id = 1})

/--
Erdős Problem #433 [ErGr80]:

For any fixed k ≥ 2, g(k,n) ∼ n²/(k-1) as n → ∞.
-/
theorem erdos_problem_433 (k : ℕ) (hk : 2 ≤ k) :
    (fun n : ℕ => (g433 k n : ℝ)) ~[atTop]
    (fun n : ℕ => (n : ℝ) ^ 2 / ((k : ℝ) - 1)) :=
  sorry
