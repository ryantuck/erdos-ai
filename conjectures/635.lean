import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #635

Let t ≥ 1 and A ⊆ {1,...,N} be such that whenever a, b ∈ A with b - a ≥ t
we have (b - a) ∤ b. How large can |A| be? Is it true that

  |A| ≤ (1/2 + o(1)) · N ?

Asked by Erdős in a letter to Ruzsa around 1980 [Gu83][Ru99].

When t = 1, the maximum is ⌊(N+1)/2⌋, achieved by taking A to be all odd
numbers in {1,...,N}. When t = 2, Erdős observed |A| ≥ N/2 + c log N for
some c > 0, by taking A to be the odd numbers together with 2^k for odd k.

The upper bound |A| ≤ (1/2 + o(1)) · N has been resolved affirmatively.
-/

/-- The divisibility-avoidance property with threshold t:
    for all a, b ∈ A with b - a ≥ t, we require (b - a) ∤ b. -/
def DivAvoidance635 (A : Finset ℕ) (t : ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, b - a ≥ t → ¬(b - a ∣ b)

/-- The maximum cardinality of a subset of {1,...,N} satisfying the
    divisibility-avoidance property with threshold t. -/
noncomputable def maxDivAvoidance635 (N t : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ DivAvoidance635 A t ∧ A.card = k}

/--
Erdős Problem #635, Part 1 (known, Erdős):

When t = 1, the maximum size of a divisibility-avoidance set in {1,...,N}
is exactly ⌊(N+1)/2⌋, achieved by taking all odd numbers.
-/
theorem erdos_problem_635_t1 (N : ℕ) (hN : N ≥ 1) :
    maxDivAvoidance635 N 1 = (N + 1) / 2 :=
  sorry

/--
Erdős Problem #635, Part 2 (Erdős):

When t = 2, there exists c > 0 such that there is a set A ⊆ {1,...,N}
satisfying the divisibility-avoidance condition with |A| ≥ N/2 + c · log N.
(Take A to be the odd numbers together with 2^k for odd k.)
-/
theorem erdos_problem_635_t2_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxDivAvoidance635 N 2 : ℝ) ≥ (N : ℝ) / 2 + c * Real.log (N : ℝ) :=
  sorry

/--
Erdős Problem #635, Main Conjecture [Gu83][Ru99] (resolved affirmatively):

For every t ≥ 1 and ε > 0, there exists N₀ such that for all N ≥ N₀,
every A ⊆ {1,...,N} satisfying the divisibility-avoidance property with
threshold t has |A| ≤ (1/2 + ε) · N.

Equivalently, maxDivAvoidance635 N t / N → 1/2 as N → ∞ for any fixed t.
-/
theorem erdos_problem_635 (t : ℕ) (ht : t ≥ 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        DivAvoidance635 A t →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ) :=
  sorry

end
