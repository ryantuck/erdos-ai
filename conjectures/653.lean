import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/--
For a configuration of n points in the Euclidean plane, R(x_i) counts the number
of distinct distances from x_i to all other points.
-/
def distinctDistances (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 2)) (i : Fin n) : ℕ :=
  ((Finset.univ.filter (· ≠ i)).image (fun j => dist (x i) (x j))).card

/--
For a configuration of n points in the Euclidean plane, the number of distinct
values that R(x_i) takes over all i.
-/
def numDistinctR (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.image (fun i => distinctDistances n x i)).card

/--
Erdős Problem #653:
Let x_1,...,x_n ∈ ℝ² and R(x_i) = #{|x_j - x_i| : j ≠ i}. Order the points
so that R(x_1) ≤ ... ≤ R(x_n). Let g(n) be the maximum number of distinct values
the R(x_i) can take. Is it true that g(n) ≥ (1-o(1))n?

Formalized as: for every ε > 0, there exists N such that for all n ≥ N,
there exists a configuration of n points in ℝ² such that the number of distinct
R-values is at least (1-ε)n.
-/
theorem erdos_problem_653_conjecture :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ x : Fin n → EuclideanSpace ℝ (Fin 2),
          (numDistinctR n x : ℝ) ≥ (1 - ε) * n :=
  sorry

end
