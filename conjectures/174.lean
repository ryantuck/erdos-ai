import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #174

A finite set A ⊂ ℝⁿ is called Ramsey if, for any k ≥ 1, there exists some
d = d(A,k) such that in any k-colouring of ℝᵈ there exists a monochromatic
copy of A. Characterise the Ramsey sets in ℝⁿ.

Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus [EGMRSS73] proved
that every Ramsey set is 'spherical': it lies on the surface of some sphere.
Graham has conjectured that every spherical set is Ramsey, which would give a
complete characterisation.

Known Ramsey sets include vertices of k-dimensional rectangles [EGMRSS73],
non-degenerate simplices [FrRo90], trapezoids [Kr92], and regular
polygons/polyhedra [Kr91].
-/

/-- A finite subset A of ℝⁿ is Euclidean Ramsey if for every k ≥ 1, there
    exists d such that any k-coloring of ℝᵈ contains a monochromatic
    isometric copy of A (i.e., a copy obtained by a distance-preserving map). -/
def IsEuclideanRamsey (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ d : ℕ, ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
      ∃ φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d),
        (∀ x y, dist (φ x) (φ y) = dist x y) ∧
        ∃ c : Fin k, ∀ a ∈ A, f (φ a) = c

/-- A finite set in ℝⁿ is spherical if all its points lie on the surface
    of some sphere (are equidistant from some center point). -/
def IsSpherical (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin n)) (r : ℝ),
    ∀ a ∈ A, dist a center = r

/--
Erdős Problem #174 / Graham's Conjecture:
A finite set A ⊂ ℝⁿ is Ramsey if and only if it is spherical.

The forward direction (Ramsey → spherical) was proved by Erdős, Graham,
Montgomery, Rothschild, Spencer, and Straus [EGMRSS73].

The reverse direction (spherical → Ramsey) is Graham's open conjecture.
-/
theorem erdos_problem_174 :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A ↔ IsSpherical n A :=
  sorry
