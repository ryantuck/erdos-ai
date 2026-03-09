import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real

noncomputable section

/--
The area of the triangle formed by three points in ℝ², computed as
½ |x₁(y₂ − y₃) + x₂(y₃ − y₁) + x₃(y₁ − y₂)|.
-/
def triangleArea (p₁ p₂ p₃ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |p₁ 0 * (p₂ 1 - p₃ 1) + p₂ 0 * (p₃ 1 - p₁ 1) + p₃ 0 * (p₁ 1 - p₂ 1)| / 2

/--
A point lies in the closed unit disk in ℝ².
-/
def inUnitDisk (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  dist p 0 ≤ 1

/--
Every point of a finite set lies in the closed unit disk.
-/
def allInUnitDisk (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, inUnitDisk p

/--
The minimum triangle area among all triples of distinct points in A.
-/
def minTriangleArea (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  ((A ×ˢ A ×ˢ A).filter (fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)).image
    (fun t => triangleArea t.1 t.2.1 t.2.2) |>.min'
    (by sorry) -- nonemptiness obligation

/--
Erdős Problem #507 [Er61,p.246] [Er75f,p.107] — Heilbronn's triangle problem:

Let α(n) be such that every set of n points in the unit disk contains three
points which determine a triangle of area at most α(n). Estimate α(n).

It is trivial that α(n) ≪ 1/n. Erdős observed that α(n) ≫ 1/n².

The current best bounds are:
  log(n) / n² ≪ α(n) ≪ 1 / n^(7/6 + o(1)).

The lower bound is due to Komlós, Pintz, and Szemerédi [KPS82].
The upper bound is due to Cohen, Pohoata, and Zakharov [CPZ24].

We formalize the lower bound (KPS82): there exists C > 0 such that for all
sufficiently large n, any set of n points in the unit disk contains three
points forming a triangle of area at most C · log(n) / n².
-/
theorem erdos_problem_507_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n →
        3 ≤ n →
        allInUnitDisk A →
        minTriangleArea A ≤ C / (n : ℝ) :=
  sorry

/--
Heilbronn's triangle problem — lower bound (Komlós–Pintz–Szemerédi):

There exists C > 0 such that for all sufficiently large n, there is a
configuration of n points in the unit disk where every triangle formed by
three of the points has area at least C · log(n) / n².
-/
theorem erdos_problem_507_lower :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ (n : ℕ), n ≥ N₀ →
        ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
          A.card = n ∧ allInUnitDisk A ∧
          ∀ p₁ ∈ A, ∀ p₂ ∈ A, ∀ p₃ ∈ A,
            p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
            triangleArea p₁ p₂ p₃ ≥ C * Real.log n / (n : ℝ) ^ 2 :=
  sorry

end
