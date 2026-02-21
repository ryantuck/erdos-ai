import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Classical

/--
A finite set A ⊆ ℕ is a "multiplicative B₂ set" (or multiplicative Sidon set) if
whenever a * b = c * d for a, b, c, d ∈ A with a < b and c < d, then a = c and b = d.
Equivalently, the pairwise products {a * b : a, b ∈ A, a < b} are all distinct.
-/
def IsMultB2 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a < b → c < d → a * b = c * d → a = c ∧ b = d

/--
A finite set A ⊆ ℕ is an "r-multiplicative Sidon set" if any two r-element
subsets of A with equal products must be the same subset.
-/
def IsMultBr (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = r → T.card = r →
    S.prod id = T.prod id → S = T

/--
F(n) is the maximum cardinality of a multiplicative B₂ subset of {1, ..., n}.
-/
noncomputable def multB2MaxSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, IsMultB2 A ∧ (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) ∧ A.card = k}

/--
Erdős Problem #425 — Part 1:

Let F(n) be the maximum size of a multiplicative B₂ subset of {1, ..., n}
(a set where all pairwise products ab with a < b are distinct).

Erdős [Er68] proved that there exist constants 0 < c₁ ≤ c₂ such that
  π(n) + c₁ n^(3/4) (log n)^(-3/2) ≤ F(n) ≤ π(n) + c₂ n^(3/4) (log n)^(-3/2).

The conjecture asks whether there exists a constant c such that
  F(n) = π(n) + (c + o(1)) n^(3/4) (log n)^(-3/2),
i.e., whether the ratio (F(n) - π(n)) / (n^(3/4) / (log n)^(3/2)) converges.
-/
theorem erdos_problem_425_part1 :
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n : ℕ =>
        ((multB2MaxSize n : ℝ) - (Nat.primeCounting n : ℝ)) /
        ((n : ℝ) ^ ((3 : ℝ) / 4) / (Real.log (n : ℝ)) ^ ((3 : ℝ) / 2)))
      Filter.atTop
      (nhds c) := by
  sorry

/--
Erdős Problem #425 — Part 2:

If A ⊆ {1, ..., n} is such that all products a₁ ⋯ aᵣ are distinct for
a₁ < ⋯ < aᵣ (i.e., A is an r-multiplicative Sidon set), then
  |A| ≤ π(n) + O(n^((r+1)/(2r))).
-/
theorem erdos_problem_425_part2 :
  ∀ r : ℕ, 2 ≤ r →
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) →
      IsMultBr r A →
      (A.card : ℝ) ≤ (Nat.primeCounting n : ℝ) + C * (n : ℝ) ^ (((r : ℝ) + 1) / (2 * (r : ℝ))) := by
  sorry
