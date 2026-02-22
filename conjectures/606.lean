import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open scoped Classical

noncomputable section

/-!
# Erdős Problem #606

Given any $n$ distinct points in $\mathbb{R}^2$, let $f(n)$ count the number of distinct
lines determined by these points. What are the possible values of $f(n)$?

A question of Grünbaum. The Sylvester-Gallai theorem implies that if the points are not
all collinear (i.e., they determine more than one line), then they determine at least $n$
lines. Erdős showed that, for some constant $c > 0$, all integers in $[cn^{3/2},
\binom{n}{2}]$ are possible except $\binom{n}{2} - 1$ and $\binom{n}{2} - 3$.

Solved (for all sufficiently large $n$) completely by Erdős and Salamon [ErSa88].

Tags: geometry
-/

/-- The number of distinct lines determined by a finite point set `A` in ℝ².
    A line is the affine span of a pair of distinct points from `A`. -/
noncomputable def numLinesDetermined
    (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (A.offDiag.image
    (fun p => affineSpan ℝ ({p.1, p.2} : Set (EuclideanSpace ℝ (Fin 2))))).card

/-- The set of achievable line counts for configurations of exactly `n` points in ℝ². -/
def achievableLineCounts (n : ℕ) : Set ℕ :=
  {k | ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ numLinesDetermined A = k}

/--
Erdős Problem #606, Sylvester-Gallai consequence [Er85]:

For any set of n ≥ 2 points in ℝ² that are not all collinear (i.e., they determine
more than 1 line), the number of distinct lines determined is at least n.
-/
theorem erdos_problem_606_sylvester_gallai :
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card ≥ 2 →
      numLinesDetermined A > 1 →
      numLinesDetermined A ≥ A.card :=
  sorry

/--
Erdős Problem #606 [Er85]:

For sufficiently large n, every integer in [c · n^(3/2), C(n,2)] is achievable
as a line count for some configuration of n points in ℝ², except for
C(n,2) - 1 and C(n,2) - 3.
-/
theorem erdos_problem_606 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      -- All values in [c·n^(3/2), C(n,2)] are achievable, except the two excluded values
      (∀ k : ℕ, (k : ℝ) ≥ c * (n : ℝ) ^ ((3 : ℝ) / 2) →
        k ≤ n.choose 2 →
        k ≠ n.choose 2 - 1 →
        k ≠ n.choose 2 - 3 →
        k ∈ achievableLineCounts n) ∧
      -- The two excluded values are never achievable
      n.choose 2 - 1 ∉ achievableLineCounts n ∧
      n.choose 2 - 3 ∉ achievableLineCounts n :=
  sorry

end
