import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #732

Call a sequence 1 < X₁ ≤ ⋯ ≤ X_m ≤ n block-compatible if there is a pairwise
balanced block design A₁, …, A_m ⊆ {1, …, n} such that |Aᵢ| = Xᵢ for 1 ≤ i ≤ m.
(A pairwise block design means every pair in {1, …, n} is contained in exactly
one Aᵢ.)

Is there some constant c > 0 such that for all large n there are
≥ exp(c · √n · log n) many block-compatible sequences for {1, …, n}?

Proved by Alon, who showed there are at least 2^{(1/2 + o(1)) · √n · log n}
block-compatible sequences. Erdős proved the upper bound exp(O(√n · log n)).
-/

/-- A pairwise balanced design (PBD) on `Fin n`: a finset of blocks where each block
    has at least 2 elements and every pair of distinct elements belongs to exactly
    one block. -/
def IsPBD (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
  (∀ i j : Fin n, i ≠ j → ∃! B, B ∈ blocks ∧ i ∈ B ∧ j ∈ B)

/-- The multiset of block sizes of a family of sets. -/
def blockSizeMultiset (n : ℕ) (blocks : Finset (Finset (Fin n))) : Multiset ℕ :=
  blocks.val.map Finset.card

/-- A multiset of natural numbers is block-compatible for n if there exists a PBD
    on Fin n with those block sizes. -/
def IsBlockCompatible (n : ℕ) (M : Multiset ℕ) : Prop :=
  ∃ blocks : Finset (Finset (Fin n)), IsPBD n blocks ∧ blockSizeMultiset n blocks = M

/--
Erdős Problem #732 [Er81]:

There exists a constant c > 0 such that for all sufficiently large n, the number
of block-compatible sequences (multisets of block sizes from PBDs on {1, …, n})
is at least exp(c · √n · log n).
-/
theorem erdos_problem_732 : ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ S : Finset (Multiset ℕ),
      (∀ M ∈ S, IsBlockCompatible n M) ∧
      (S.card : ℝ) ≥ Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) :=
  sorry

end
