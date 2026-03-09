import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

/--
The Hofstadter–Erdős set is the smallest set S ⊆ ℕ containing 2 and 3 that is
closed under (a, b) ↦ a * b - 1 for distinct a, b ∈ S. This is OEIS A005244.
We define it as the intersection of all such closed sets.
-/
def HofstadterErdosSet : Set ℕ :=
  ⋂₀ {S : Set ℕ | 2 ∈ S ∧ 3 ∈ S ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a * b - 1 ∈ S}

/--
A set A ⊆ ℕ has **positive upper density** if
  lim sup_{N → ∞} |A ∩ {1, …, N}| / N > 0.
We express this as: there exists δ > 0 such that for infinitely many N,
|A ∩ {1, …, N}| ≥ δ · N.
-/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      (A ∩ Set.Icc 1 N).ncard ≥ δ * (N : ℝ)

/--
Erdős Problem #424 [Er77c, ErGr80]:

Let a₁ = 2 and a₂ = 3 and continue the sequence by appending all possible
values aᵢ · aⱼ - 1 with i ≠ j. Is it true that the set of integers which
eventually appear has positive density?

Asked by Hofstadter. The sequence begins 2, 3, 5, 9, 14, 17, 26, … and is
A005244 in the OEIS. No integer ≡ 1 (mod 3) ever appears, so the density is
at most 2/3.
-/
theorem erdos_problem_424 :
    HasPositiveUpperDensity HofstadterErdosSet :=
  sorry
