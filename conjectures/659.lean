import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Classical

/-!
# Erdős Problem #659

Is there a set of n points in ℝ² such that every subset of 4 points determines
at least 3 distinct distances, yet the total number of distinct distances is
≪ n / √(log n)?

Erdős believed this should be possible. It was answered in the AFFIRMATIVE:
a suitable truncation of the lattice {(a, b√2) : a,b ∈ ℤ} suffices. This
construction was first considered by Moree and Osburn [MoOs06] and independently
by Lund and Sheffer, who further noted that the configuration contains no
squares or equilateral triangles. Grayzel (using Gemini) completed the proof
by ruling out the remaining four-point two-distance configuration.
-/

/-- The number of distinct pairwise distances in a finite point set A ⊆ ℝ². -/
noncomputable def numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set A ⊆ ℝ² satisfies the "four-point, three-distance" property
    if every 4-element subset determines at least 3 distinct pairwise distances. -/
def FourPointThreeDist (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 4 → 3 ≤ numDistances S

/--
Erdős Problem #659 [Er97e, p.531]:
There exists an absolute constant C > 0 such that for every sufficiently large n,
there is a set A of n points in ℝ² with the four-point-three-distance property
(every 4-point subset determines at least 3 distinct distances) whose total
number of distinct distances satisfies |distances(A)| ≤ C · n / √(log n).
-/
theorem erdos_problem_659 :
    ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
          A.card = n ∧
          FourPointThreeDist A ∧
          (numDistances A : ℝ) ≤ C * n / Real.sqrt (Real.log n) :=
  sorry
