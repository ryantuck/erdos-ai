import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/--
A finite point set in ℝ² has no (k+1) collinear points if every (k+1)-element
subset is not collinear (i.e., no line contains k+1 or more of the points).
-/
def NoKPlusOneCollinear (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = k + 1 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of k-rich lines: the number of distinct affine lines in ℝ² that
contain at least k points from P.
-/
noncomputable def kRichLineCount (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #588:
Let f_k(n) be the maximum number of lines containing at least k points,
over all configurations of n points in ℝ² with no k+1 collinear.
Is it true that f_k(n) = o(n²) for all k ≥ 4?

This is a generalisation of Problem #101 (the case k = 4). The restriction
to k ≥ 4 is necessary since Sylvester showed f_3(n) = n²/6 + O(n).

Formally: for every k ≥ 4 and every ε > 0, there exists N such that for
all n ≥ N and every set P of n points in ℝ² with no k+1 collinear, the
count of k-rich lines is at most ε · n².
-/
theorem erdos_problem_588 :
  ∀ k : ℕ, k ≥ 4 →
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          NoKPlusOneCollinear k P →
          (kRichLineCount k P : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry
