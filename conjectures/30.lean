import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/--
A finite set of natural numbers is a **Sidon set** (or B₂ set) if all pairwise
sums are distinct: for a, b, c, d ∈ A with a ≤ b and c ≤ d,
a + b = c + d implies a = c and b = d.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
h(N) is the maximum size of a Sidon set contained in {1, …, N}.
-/
noncomputable def sidonMaxCard (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ IsSidonSet A ∧ A.card = k}

/--
Erdős Problem #30 [Er61, Er69, Er70b, Er70c, Er72, Er73, Er77c, Er80e, Er81,
Er81h, Er91, Er92c, Er94b, Er95, Er97c, Va99]:

Let h(N) be the maximum size of a Sidon set in {1,…,N}. Is it true that, for
every ε > 0,
  h(N) = N^{1/2} + O_ε(N^ε)?

A problem of Erdős and Turán ($1000 prize). Erdős and Turán proved
h(N) ≤ N^{1/2} + N^{1/4} + 1. Singer showed h(N) ≥ (1 - o(1))N^{1/2}.
-/
theorem erdos_problem_30 :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 0 < N →
          |((sidonMaxCard N : ℝ) - (N : ℝ) ^ ((1 : ℝ) / 2))| ≤ C * (N : ℝ) ^ ε :=
  sorry
