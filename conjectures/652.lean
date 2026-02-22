import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

open Classical

/-!
# Erdős Problem #652

Let $x_1, \ldots, x_n \in \mathbb{R}^2$ and let
$R(x_i) = \#\{ |x_j - x_i| : j \neq i \}$, where the points are ordered such that
$R(x_1) \leq \cdots \leq R(x_n)$.

Let $\alpha_k$ be minimal such that, for all large enough $n$, there exists a set of
$n$ points with $R(x_k) < \alpha_k n^{1/2}$.

Is it true that $\alpha_k \to \infty$ as $k \to \infty$?

This was proved in the affirmative. Mathialagan [Ma21] showed that given sets $P$
($k$ points) and $Q$ ($n$ points) with $2 \leq k \leq n^{1/3}$, some point of $P$
determines $\gg (kn)^{1/2}$ distances to $Q$, implying
$R(x_k) \gg (kn)^{1/2}$ for $2 \leq k \leq n^{1/3}$.
-/

/--
The number of distinct distances from a point `p` to other points in a finite set
`S ⊂ ℝ²`. That is, `R(p) = #{dist(p, q) : q ∈ S, q ≠ p}`.
-/
def numDistinctDistances (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((S.filter (· ≠ p)).image (dist p)).card

/--
Erdős Problem #652:

The conjecture that `αₖ → ∞` is equivalent to: for every constant `C > 0`, for all
sufficiently large `k`, there are infinitely many `n` such that every set of `n` points
in `ℝ²` has fewer than `k` points with fewer than `C√n` distinct distances to the rest
of the set.
-/
theorem erdos_problem_652 :
    ∀ C : ℝ, C > 0 →
      ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
        ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
          ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n →
            (S.filter (fun p =>
              (numDistinctDistances p S : ℝ) < C * Real.sqrt (↑n))).card < k :=
  sorry

end
