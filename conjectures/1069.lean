import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open Classical

noncomputable section

/-!
# Erdős Problem #1069

Given any n points in ℝ², the number of k-rich lines (lines containing ≥ k
of the points) is ≪ n²/k³, provided k ≤ √n.

Conjectured by Erdős, Croft, and Purdy [Er87b]. Proved by Szemerédi and
Trotter [SzTr83].
-/

/-- A line in ℝ² (represented as `Fin 2 → ℝ`): a set of the form
    `{p + t • d | t : ℝ}` for some point `p` and nonzero direction `d`. -/
def IsLine (L : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (p d : Fin 2 → ℝ), d ≠ 0 ∧ L = {q : Fin 2 → ℝ | ∃ t : ℝ, q = p + t • d}

/-- The number of k-rich lines determined by a finite point set S ⊆ ℝ²:
    lines containing at least k points of S. -/
def numKRichLines (S : Finset (Fin 2 → ℝ)) (k : ℕ) : ℕ :=
  Set.ncard {L : Set (Fin 2 → ℝ) | IsLine L ∧ k ≤ (S.filter (· ∈ L)).card}

/--
Erdős Problem #1069 (Szemerédi–Trotter theorem) [Er87b, p.169]:

There exists a constant C > 0 such that for any finite set S of n points in ℝ²
and any integer k with 2 ≤ k and k² ≤ n, the number of lines containing at
least k points of S is at most C · n² / k³.
-/
theorem erdos_problem_1069 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (S : Finset (Fin 2 → ℝ)) (k : ℕ),
      2 ≤ k → (k : ℝ) ^ 2 ≤ (S.card : ℝ) →
      (numKRichLines S k : ℝ) ≤ C * (S.card : ℝ) ^ 2 / (k : ℝ) ^ 3 :=
  sorry

end
