import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Complex Finset

noncomputable section

/--
Erdős Problem #1041 [EHP58, p.139]:

Let f(z) = ∏ᵢ (z - zᵢ) ∈ ℂ[z] with |zᵢ| < 1 for all i. Must there always
exist a path of length less than 2 in {z : |f(z)| < 1} which connects two of
the roots of f?

A problem of Erdős, Herzog, and Piranian, who proved that the sublevel set
{z : |f(z)| < 1} always has a connected component containing at least two roots.
-/
theorem erdos_problem_1041 :
    ∀ (n : ℕ) (hn : 2 ≤ n) (roots : Fin n → ℂ),
      (∀ i, ‖roots i‖ < 1) →
      ∃ (i j : Fin n), i ≠ j ∧
        ∃ (γ : Path (roots i) (roots j)),
          (∀ t, ‖∏ k : Fin n, (γ t - roots k)‖ < 1) ∧
          eVariationOn γ.extend (Set.Icc 0 1) < 2 :=
  sorry

end
