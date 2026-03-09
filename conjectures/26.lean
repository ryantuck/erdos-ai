import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Cofinite

open scoped Classical
open Finset

/--
The natural density of a set S ⊆ ℕ is 1, i.e., "almost all" natural numbers
belong to S:  |S ∩ {1,…,N}| / N → 1  as N → ∞.
Expressed as: for every ε > 0, for all sufficiently large N,
|S ∩ {1,…,N}| ≥ (1 - ε) * N.
-/
noncomputable def HasDensityOne (S : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) ≥ (1 - ε) * N

/--
The set of natural numbers that have a divisor in a given set B.
That is, {n ∈ ℕ | ∃ b ∈ B, b ∣ n}.
-/
def HasDivisorIn (B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ b ∈ B, b ∣ n}

/--
A set B ⊆ ℕ is a **Behrend sequence** if almost all natural numbers
have a divisor in B, i.e., the set {n | ∃ b ∈ B, b ∣ n} has density 1.
-/
def IsBehrendSeq (B : Set ℕ) : Prop :=
  HasDensityOne (HasDivisorIn B)

/--
The translate of a set A by k: {a + k | a ∈ A}.
-/
def SetTranslate (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, n = a + k}

/--
Erdős Problem #26 [Er95,p.167]:

Let A ⊂ ℕ be infinite. Must there exist some k ≥ 1 such that almost all
integers have a divisor of the form a + k for some a ∈ A?

Equivalently: does there exist k ≥ 1 such that A + k is a Behrend sequence?

Asked by Erdős and Tenenbaum. The answer is **no** (DISPROVED).
Ruzsa gave a simple counterexample. Davenport and Erdős showed that
∑ 1/a = ∞ for every Behrend sequence, so taking any infinite A with
∑ 1/a < ∞ immediately gives a counterexample.
-/
theorem erdos_problem_26 :
    ¬ (∀ (A : Set ℕ), A.Infinite →
      ∃ k : ℕ, 0 < k ∧ IsBehrendSeq (SetTranslate A k)) :=
  sorry
