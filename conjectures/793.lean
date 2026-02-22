import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Classical

/--
A finite set A ⊆ ℕ is "primitive-like" (for this problem) if no element divides
the product of two other elements: for all a, b, c ∈ A with a ≠ b and a ≠ c,
a does not divide b * c.
-/
def IsPrimitiveLike (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → ¬(a ∣ b * c)

/--
F(n) is the maximum cardinality of a primitive-like subset of {1, ..., n}.
-/
noncomputable def primitiveLikeMaxSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, IsPrimitiveLike A ∧ (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) ∧ A.card = k}

/-!
# Erdős Problem #793

Let F(n) be the maximum possible size of a subset A ⊆ {1, …, n} such that
a ∤ bc whenever a, b, c ∈ A with a ≠ b and a ≠ c. Is there a constant C
such that

  F(n) = π(n) + (C + o(1)) · n^{2/3} · (log n)^{-2}?

Erdős [Er38] proved there exist constants 0 < c₁ ≤ c₂ such that
  π(n) + c₁ · n^{2/3} · (log n)^{-2} ≤ F(n) ≤ π(n) + c₂ · n^{2/3} · (log n)^{-2}.

See also problem #425.
-/

/--
Erdős Problem #793 [Er69][Er70b]:

The conjecture asks whether there exists a constant C such that
  F(n) = π(n) + (C + o(1)) · n^{2/3} · (log n)^{-2},
i.e., whether the ratio (F(n) - π(n)) / (n^{2/3} / (log n)^2) converges.
-/
theorem erdos_problem_793 :
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n : ℕ =>
        ((primitiveLikeMaxSize n : ℝ) - (Nat.primeCounting n : ℝ)) /
        ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log (n : ℝ)) ^ (2 : ℝ)))
      Filter.atTop
      (nhds c) := by
  sorry
