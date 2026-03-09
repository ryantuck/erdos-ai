import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Classical

noncomputable section

/--
A set S ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are distinct:
whenever a + b = c + d with a ≤ b and c ≤ d, all from S, then a = c and b = d.
-/
def IsSidonSet (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/--
The **greedy Sidon sequence** (Mian–Chowla sequence) A = {1,2,4,8,13,21,31,45,…}
is the lexicographically smallest infinite Sidon subset of ℕ starting from 1.
Equivalently, A is a Sidon set with 1 ∈ A, and every positive integer n ∉ A was
skipped because adding it to the elements of A below n would violate the Sidon property.
-/
def IsGreedySidonSequence (A : Set ℕ) : Prop :=
  IsSidonSet A ∧ 1 ∈ A ∧
    ∀ n : ℕ, n ≥ 1 → n ∉ A → ¬IsSidonSet ({m ∈ A | m < n} ∪ {n})

/--
Counting function: the number of elements of A in {1, …, N}.
-/
noncomputable def countInInterval (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => n ∈ A ∧ 1 ≤ n)).card

/--
Erdős Problem #340 [ErGr80, p.53]:

Let A = {1,2,4,8,13,21,31,45,66,81,97,…} be the greedy Sidon sequence (Mian–Chowla
sequence): we begin with 1 and iteratively include the next smallest integer that
preserves the Sidon property. Is it true that

  |A ∩ {1,…,N}| ≫ N^{1/2 - ε}

for all ε > 0 and large N?
-/
theorem erdos_problem_340 :
    ∀ A : Set ℕ, IsGreedySidonSequence A →
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (countInInterval A N : ℝ) ≥ (N : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
  sorry

end
