import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

open Finset Classical

noncomputable section

/-!
# Erdős Problem #654

Let f(n) be such that, given any x₁, ..., xₙ ∈ ℝ² with no four points on a
circle, there exists some xᵢ with at least f(n) many distinct distances to
other xⱼ. Is it true that f(n) > (1/3 + c)n for some c > 0, for all large n?

The trivial bound is f(n) ≥ (n-1)/3. The stronger conjecture f(n) > (1-o(1))n
was disproved by Aletheia [Fe26].

A problem of Erdős and Pach [Er87b][ErPa90][Er97e].
-/

/-- Squared Euclidean distance between two points in ℝ². -/
def sqEuclideanDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Four points in ℝ² are concyclic if they all lie on a common circle
    (with positive radius). Expressed using squared distances. -/
def FourConcyclic (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  ∃ (c : ℝ × ℝ) (r_sq : ℝ), r_sq > 0 ∧
    sqEuclideanDist p₁ c = r_sq ∧ sqEuclideanDist p₂ c = r_sq ∧
    sqEuclideanDist p₃ c = r_sq ∧ sqEuclideanDist p₄ c = r_sq

/-- A configuration of n points in ℝ² has no four concyclic points
    if no four distinct points lie on a common circle. -/
def NoFourConcyclic (n : ℕ) (pts : Fin n → ℝ × ℝ) : Prop :=
  ∀ (i₁ i₂ i₃ i₄ : Fin n),
    i₁ ≠ i₂ → i₁ ≠ i₃ → i₁ ≠ i₄ → i₂ ≠ i₃ → i₂ ≠ i₄ → i₃ ≠ i₄ →
    ¬FourConcyclic (pts i₁) (pts i₂) (pts i₃) (pts i₄)

/-- The number of distinct distances from point i to all other points in the
    configuration. Uses squared distances since d(p,q) = d(p',q') iff
    sqDist(p,q) = sqDist(p',q') for nonnegative distances. -/
def numDistinctDistances (n : ℕ) (pts : Fin n → ℝ × ℝ) (i : Fin n) : ℕ :=
  ((univ.filter (· ≠ i)).image (fun j => sqEuclideanDist (pts i) (pts j))).card

/--
Erdős Problem #654 [Er87b][ErPa90][Er97e]:

There exists a constant c > 0 such that for all sufficiently large n,
given any n points in ℝ² with no four on a circle, there exists some
point with at least (1/3 + c) · n distinct distances to the other points.
-/
theorem erdos_problem_654 :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ pts : Fin n → ℝ × ℝ, Function.Injective pts →
        NoFourConcyclic n pts →
        ∃ i : Fin n, (numDistinctDistances n pts i : ℝ) > (1 / 3 + c) * ↑n :=
  sorry

end
