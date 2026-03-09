import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
A finite set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are
distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have
{a, b} = {c, d}.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
The sumset A + A of a finite set A ⊆ ℕ.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
Given a sorted list of natural numbers, compute the sum of squared consecutive
gaps: Σᵢ (sᵢ₊₁ - sᵢ)².
-/
def sumSquaredGaps : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)

/--
Erdős Problem #153 [ESS94]:

Let A be a finite Sidon set and A + A = {s₁ < ⋯ < sₜ}. Is it true that
  (1/t) · Σᵢ (sᵢ₊₁ - sᵢ)² → ∞
as |A| → ∞?

Formally: for every M ≥ 1, there exists N such that for every Sidon set A
with |A| ≥ N, if we sort A + A into a list s of length t, then
  sumSquaredGaps(s) ≥ M * t.
-/
theorem erdos_problem_153 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ (A : Finset ℕ),
      IsSidonSet A →
      N ≤ A.card →
      let S := (sumset A).sort (· ≤ ·)
      M * S.length ≤ sumSquaredGaps S :=
  sorry
