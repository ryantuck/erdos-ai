import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph Real BigOperators

/-!
# Erdős Problem #191

Let C > 0 be arbitrary. Is it true that, if n is sufficiently large depending on C,
then in any 2-colouring of the pairs from {2, ..., n} there exists some
X ⊆ {2, ..., n} such that all pairs from X are monochromatic and
∑ x ∈ X, 1 / log x ≥ C?

A 2-colouring of pairs is modeled as a SimpleGraph on ℕ (edges = colour 1,
non-edges = colour 2). A monochromatic set is a clique in either G or its
complement Gᶜ.

The answer is yes, proved by Rödl [Ro03]. Conlon, Fox, and Sudakov [CFS13]
proved the optimal quantitative bound: in any 2-colouring one can find such X
with ∑ 1/log x ≥ c · log log log n.
-/

/--
Erdős Problem #191 [ErGr79, ErGr80, Er81, Er82e]:
For any C > 0, if n is sufficiently large (depending on C), then in any
2-colouring of the pairs from {2, ..., n}, there exists a monochromatic
set X ⊆ {2, ..., n} with ∑ x ∈ X, 1 / log x ≥ C.
-/
theorem erdos_problem_191_conjecture :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ∀ G : SimpleGraph ℕ,
          ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
            (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
            C ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) := by
  sorry
