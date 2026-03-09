import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

open Finset

/--
A set of points in ℝ² is **non-trilinear** (or "no three on a line") if no
three distinct points in the set are collinear.
-/
def NoThreeCollinear (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (EuclideanSpace ℝ (Fin 2)))

/--
A set A ⊂ ℝ² is **ε-non-trilinear** if every finite subset B ⊆ A of size n
contains a subset C of size ≥ εn with no three collinear.
-/
def EpsNonTrilinear (A : Set (EuclideanSpace ℝ (Fin 2))) (ε : ℝ) : Prop :=
  ∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
    (↑B : Set (EuclideanSpace ℝ (Fin 2))) ⊆ A →
    ∃ C : Finset (EuclideanSpace ℝ (Fin 2)),
      (↑C : Set (EuclideanSpace ℝ (Fin 2))) ⊆ ↑B ∧
      ε * B.card ≤ C.card ∧
      NoThreeCollinear (↑C : Set (EuclideanSpace ℝ (Fin 2)))

/--
A set A ⊂ ℝ² is **weakly non-trilinear** if it is the union of finitely many
sets, each with no three collinear.
-/
def WeaklyNonTrilinear846 (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (k : ℕ) (F : Fin k → Set (EuclideanSpace ℝ (Fin 2))),
    (∀ i, NoThreeCollinear (F i)) ∧
    A ⊆ ⋃ i, F i

/--
Erdős Problem #846 [Er92b]:

Let A ⊂ ℝ² be an infinite set for which there exists some ε > 0 such that in
any subset of A of size n there are always at least εn with no three on a line.

Is it true that A is the union of a finite number of sets where no three are on
a line?

A problem of Erdős, Nešetřil, and Rödl. The answer is **no** (disproved).
-/
theorem erdos_problem_846 :
    ¬(∀ (A : Set (EuclideanSpace ℝ (Fin 2))),
      A.Infinite →
      (∃ ε : ℝ, 0 < ε ∧ EpsNonTrilinear A ε) →
      WeaklyNonTrilinear846 A) :=
  sorry
