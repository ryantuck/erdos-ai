import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Classical

noncomputable section

/-!
# Erdős Problem #604

Given $n$ distinct points $A \subset \mathbb{R}^2$, must there be a point $x \in A$ such that
$$\#\{ d(x,y) : y \in A\} \gg n/\sqrt{\log n}?$$

This is the pinned distance problem, a stronger form of Problem #89 (the distinct
distances problem). The example of an integer grid shows that $n/\sqrt{\log n}$ would
be best possible.

The best known bound is $\gg n^{c - o(1)}$ where $c = (48 - 14e)/(55 - 16e) = 0.8641...$,
due to Katz and Tardos.

Tags: geometry, distances
-/

/--
The set of distinct distances from a point `x` to all points in a finite set `A` in ℝ².
-/
noncomputable def pinnedDistances (x : EuclideanSpace ℝ (Fin 2))
    (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  A.image (fun y => dist x y)

/--
Erdős Problem #604 [Er57][Er61]:

Given n distinct points A ⊂ ℝ², there must exist a point x ∈ A such that the number
of distinct distances from x to other points in A is ≫ n/√(log n).

Formally: there exists a constant C > 0 and a threshold N₀ such that for all n ≥ N₀
and every set A of n points in ℝ², some point x ∈ A has at least C · n / √(log n)
distinct pinned distances.

The integer grid shows this would be best possible.
-/
theorem erdos_problem_604 :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        A.card = n →
        ∃ x ∈ A, ((pinnedDistances x A).card : ℝ) ≥
          C * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
  sorry

end
