import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

noncomputable section

/-!
# Erdős Problem #776

Let r ≥ 2 and A_1, …, A_m ⊆ {1, …, n} be such that A_i ⊄ A_j for all
i ≠ j (an antichain) and for any t, if there exists some i with |A_i| = t
then there must exist at least r sets of that size.

How large must n be (as a function of r) to ensure that there is such a
family which achieves n − 3 distinct sizes of sets?

A problem of Erdős and Trotter. For r = 1 and n > 3 the maximum possible
is n − 2. For r > 1 and n sufficiently large n − 3 is achievable, but
n − 2 is never achievable.

https://www.erdosproblems.com/776

Tags: combinatorics
-/

/-- A family of sets is an antichain if no set is a subset of another. -/
def IsAntichain776 (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬(A ⊆ B)

/-- Every size that appears in the family appears at least r times. -/
def HasMinMultiplicity776 (F : Finset (Finset ℕ)) (r : ℕ) : Prop :=
  ∀ t : ℕ, (∃ A ∈ F, A.card = t) →
    r ≤ (F.filter (fun A => A.card = t)).card

/-- The number of distinct sizes of sets in the family. -/
def numDistinctSizes776 (F : Finset (Finset ℕ)) : ℕ :=
  (F.image Finset.card).card

/-- All sets in the family are subsets of {1, …, n}, modelled as subsets of Fin n
    (equivalently, subsets of {0, …, n-1}). -/
def AllSubsetsOfRange776 (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ A ∈ F, ∀ x ∈ A, x < n

/--
Erdős Problem #776 (OPEN):

For every r ≥ 2, there exists N₀ such that for all n ≥ N₀ there is an antichain
F of subsets of {0, …, n-1} in which every size class has at least r members
and the family achieves exactly n − 3 distinct sizes of sets.

The problem asks for the growth rate of N₀ as a function of r.
-/
theorem erdos_problem_776 :
    ∀ r : ℕ, r ≥ 2 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ F : Finset (Finset ℕ),
          AllSubsetsOfRange776 F n ∧
          IsAntichain776 F ∧
          HasMinMultiplicity776 F r ∧
          numDistinctSizes776 F = n - 3 :=
  sorry

/--
For r = 1 and n > 3, an antichain of subsets of {0, …, n-1} can achieve
at most n − 2 distinct sizes, and this is tight.
-/
theorem erdos_problem_776_r_eq_1 :
    ∀ n : ℕ, n > 3 →
      (∃ F : Finset (Finset ℕ),
        AllSubsetsOfRange776 F n ∧
        IsAntichain776 F ∧
        numDistinctSizes776 F = n - 2) ∧
      (∀ F : Finset (Finset ℕ),
        AllSubsetsOfRange776 F n →
        IsAntichain776 F →
        numDistinctSizes776 F ≤ n - 2) :=
  sorry

/--
For r ≥ 2, no antichain with minimum multiplicity r can achieve n − 2
distinct sizes (for any n).
-/
theorem erdos_problem_776_upper_bound :
    ∀ r : ℕ, r ≥ 2 → ∀ n : ℕ,
      ∀ F : Finset (Finset ℕ),
        AllSubsetsOfRange776 F n →
        IsAntichain776 F →
        HasMinMultiplicity776 F r →
        numDistinctSizes776 F ≤ n - 3 :=
  sorry

end
