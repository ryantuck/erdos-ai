import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
A finite set of natural numbers contains a k-term arithmetic progression
if there exist natural numbers a and d with d ≥ 1 such that
a + i * d ∈ A for all 0 ≤ i < k.
-/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≥ 1 ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/--
The number of k-term arithmetic progressions in A, counted as pairs (a, d)
with d ≥ 1 such that a + i * d ∈ A for all 0 ≤ i < k.
-/
def numAP (A : Finset ℕ) (k : ℕ) : ℕ :=
  if h : A.Nonempty then
    let M := A.max' h
    ((Finset.Icc 0 M ×ˢ Finset.Icc 1 M).filter
      fun p => ∀ i ∈ Finset.range k, p.1 + i * p.2 ∈ A).card
  else 0

/--
Erdős Problem #179, Part 1:
Let 1 ≤ k < ℓ be integers and define F_k(N, ℓ) to be the minimum number of
k-term arithmetic progressions that an N-element set A ⊆ ℕ must contain to
guarantee an ℓ-term arithmetic progression. Is it true that F_3(N, 4) = o(N²)?

Proved by Fox and Pohoata [FoPo20].
-/
theorem erdos_problem_179_part1 :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ, A.card = N →
    (numAP A 3 : ℝ) ≥ ε * (N : ℝ) ^ 2 →
    ContainsAP A 4 :=
  sorry

/--
Erdős Problem #179, Part 2:
For every ℓ > 3, lim_{N→∞} log F_3(N,ℓ) / log N = 2.
The nontrivial direction: for every ε > 0, for sufficiently large N,
there exists an N-element set with at least N^(2-ε) three-term arithmetic
progressions but no ℓ-term arithmetic progression.

Proved by Fox and Pohoata [FoPo20].
-/
theorem erdos_problem_179_part2 :
    ∀ ℓ : ℕ, ℓ > 3 → ∀ ε : ℝ, ε > 0 → ε < 2 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∃ A : Finset ℕ, A.card = N ∧
    (numAP A 3 : ℝ) ≥ (N : ℝ) ^ (2 - ε) ∧
    ¬ContainsAP A ℓ :=
  sorry
