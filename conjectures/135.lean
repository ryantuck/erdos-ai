import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #135

Let A ⊆ ℝ² be a set of n points such that any subset of size 4 determines
at least 5 distinct distances. Must A determine ≫ n² many distances?

Answered in the NEGATIVE by Tao (2024): for any large n there exists a set
of n points in ℝ² such that any 4 points determine at least 5 distinct
distances, yet the total number of distinct distances is O(n²/√(log n)).
-/

/-- The number of distinct pairwise distances in a finite point set A ⊆ ℝ². -/
noncomputable def numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set A ⊆ ℝ² satisfies the "four-point, five-distance" property
    if every 4-element subset determines at least 5 distinct pairwise distances. -/
def FourPointFiveDist (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 4 → 5 ≤ numDistances S

/--
Erdős–Gyárfás Conjecture (Problem #135) [Er97b, Er97e]:
Let A ⊆ ℝ² be a set of n points such that any 4 points determine at least 5
distinct distances. Must A determine ≫ n² many distances?

The conjecture asserts YES: there exists an absolute constant c > 0 such that
every finite A ⊆ ℝ² with the four-point-five-distance property satisfies
|distinct distances of A| ≥ c · n².

This was answered in the NEGATIVE by Tao [Ta24c], who constructed for any
large n a set of n points where any 4 points determine at least 5 distinct
distances, yet the number of distinct distances is O(n²/√(log n)).
-/
theorem erdos_problem_135 :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        FourPointFiveDist A →
        c * (A.card : ℝ) ^ 2 ≤ (numDistances A : ℝ) :=
  sorry
