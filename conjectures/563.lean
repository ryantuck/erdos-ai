import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #563

Let F(n, α) denote the smallest m such that there exists a 2-colouring of the
edges of K_n so that every X ⊆ [n] with |X| ≥ m contains more than
α · C(|X|, 2) edges of each colour.

Prove that, for every 0 ≤ α < 1/2,
  F(n, α) ~ c_α · log n
for some constant c_α depending only on α.
-/

/-- The number of edges of a given colour within a subset X, where the colouring
    is given by a symmetric function `c : Fin n → Fin n → Bool`. An edge {i, j}
    (with i < j in the natural ordering on Fin n) has colour `c i j`. -/
def edgesOfColorInSubset {n : ℕ} (c : Fin n → Fin n → Bool)
    (X : Finset (Fin n)) (color : Bool) : ℕ :=
  ((X ×ˢ X).filter (fun p => p.1 < p.2 ∧ c p.1 p.2 = color)).card

/-- F(n, α): the smallest m such that there exists a 2-colouring of the edges
    of K_n such that every subset of vertices of size ≥ m contains more than
    α · C(|X|, 2) edges of each colour. -/
noncomputable def F_erdos563 (n : ℕ) (α : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ (c : Fin n → Fin n → Bool),
    (∀ i j, c i j = c j i) ∧
    ∀ X : Finset (Fin n), (X.card : ℝ) ≥ (m : ℝ) →
      ∀ color : Bool,
        (edgesOfColorInSubset c X color : ℝ) >
          α * ((X.card : ℝ) * ((X.card : ℝ) - 1) / 2)}

/--
Erdős Problem #563 [Er90b]:

For every 0 ≤ α < 1/2, there exists a constant c_α > 0 such that
  F(n, α) ~ c_α · log n,
i.e., F(n, α) / log(n) → c_α as n → ∞.
-/
theorem erdos_problem_563 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun n : ℕ => (F_erdos563 n α : ℝ) / Real.log (n : ℝ))
        atTop (nhds c) :=
  sorry

end
