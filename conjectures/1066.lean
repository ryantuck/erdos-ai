import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

noncomputable section

/-!
# Erdős Problem #1066

Let G be a graph given by n points in ℝ², where any two distinct points are
at least distance 1 apart, and we draw an edge between two points if they are
distance 1 apart.

Let g(n) be maximal such that any such graph always has an independent set on
at least g(n) vertices. Estimate g(n), or perhaps lim g(n)/n.

Such graphs are always planar. The current record bounds are
  (8/31)n ≤ g(n) ≤ (5/16)n.
The lower bound is due to Swanepoel [Sw02] and the upper bound to Pach and
Tóth [PaTo96].
-/

/--
**Erdős Problem #1066**, lower bound [Sw02]:

For every n ≥ 1 and every injective placement of n points in ℝ² with all
pairwise distances ≥ 1, there exists a set of at least (8/31)n points with
no two at distance exactly 1 (an independent set in the unit distance graph).
-/
theorem erdos_problem_1066_lower (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2))
    (hf_inj : Function.Injective f)
    (hf_min : ∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 8 / 31 * (n : ℝ) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 :=
  sorry

/--
**Erdős Problem #1066**, upper bound [PaTo96]:

For all sufficiently large n, there exists an injective placement of n points
in ℝ² with all pairwise distances ≥ 1 such that every independent set in the
unit distance graph has size at most (5/16)n.
-/
theorem erdos_problem_1066_upper :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        Function.Injective f ∧
        (∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) ∧
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ 5 / 16 * (n : ℝ) :=
  sorry

end
