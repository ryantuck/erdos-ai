import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #875

Let A = {a₁ < a₂ < ⋯} ⊂ ℕ be an infinite set such that the sets
  S_r = { a₁ + ⋯ + aᵣ : a₁ < ⋯ < aᵣ ∈ A }
are disjoint for distinct r ≥ 1. How fast can such a sequence grow?
How small can a_{n+1} - a_n be? In particular, for which c is it possible
that a_{n+1} - a_n ≤ n^c?

A problem of Deshouillers and Erdős (an infinite version of problem #874).
Such sets are sometimes called admissible. Erdős writes 'it [is not]
completely trivial to find such a sequence for which a_{n+1}/a_n → 1'.

https://www.erdosproblems.com/875
-/

/-- The set of r-fold subset sums of a set A ⊆ ℕ: all sums a₁ + ⋯ + aᵣ
    where a₁, …, aᵣ are r distinct elements of A. -/
def rSubsetSumsInf (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {s | ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ A ∧ S.card = r ∧ S.sum id = s}

/-- An infinite set A ⊆ ℕ is *admissible* if the r-fold subset sums S_r are
    pairwise disjoint for all distinct r₁ ≠ r₂ with r₁, r₂ ≥ 1. -/
def IsAdmissibleInf (A : Set ℕ) : Prop :=
  ∀ r₁ r₂ : ℕ, 1 ≤ r₁ → 1 ≤ r₂ → r₁ ≠ r₂ →
    Disjoint (rSubsetSumsInf A r₁) (rSubsetSumsInf A r₂)

/--
Erdős Problem #875, part (a):

There exists an infinite admissible set A = {a₁ < a₂ < ⋯} such that
a_{n+1}/a_n → 1 as n → ∞.

Formulated as: for every ε > 0, eventually a(n+1) ≤ (1 + ε) · a(n).
-/
theorem erdos_problem_875_ratio :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsAdmissibleInf (Set.range a) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (a (n + 1) : ℝ) ≤ (1 + ε) * (a n : ℝ) :=
  sorry

/--
Erdős Problem #875, part (b):

Determine for which c > 0 there exists an infinite admissible set
A = {a₁ < a₂ < ⋯} such that a_{n+1} - a_n ≤ n^c for all sufficiently large n.

Formalized as: there exists c > 0 and an infinite admissible sequence whose
gaps satisfy a(n+1) - a(n) ≤ n^c eventually.
-/
theorem erdos_problem_875_gap :
    ∃ c : ℝ, c > 0 ∧
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsAdmissibleInf (Set.range a) ∧
      ∀ᶠ n : ℕ in atTop,
        (a (n + 1) : ℝ) - (a n : ℝ) ≤ (n : ℝ) ^ c :=
  sorry

end
