import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #957

Let $A \subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1 < \ldots < d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the number of
(unordered) pairs of points at distance $d$. Is it true that
$$f(d_1) f(d_k) \leq \left(\frac{9}{8} + o(1)\right) n^2?$$

A question of Erdős and Pach [ErPa90]. An unpublished construction of Makai
shows that this would be the best possible. Solved by Dumitrescu [Du19], who
proved $f(d_1) f(d_k) \leq \frac{9}{8} n^2 + O(n)$.

See also problems #132 and #756.
-/

/-- The number of unordered pairs of distinct points in $A$ at Euclidean
    distance $d$. Computed as the number of ordered pairs divided by 2. -/
noncomputable def distFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/--
Erdős Problem #957 [ErPa90] (proved by Dumitrescu [Du19]):
For every $\varepsilon > 0$, for all sufficiently large finite point sets
$A \subset \mathbb{R}^2$, the product of the frequency of the minimum distance
and the frequency of the maximum distance satisfies
$f(d_{\min}) \cdot f(d_{\max}) \leq (9/8 + \varepsilon) \cdot |A|^2$.
-/
theorem erdos_problem_957 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), N₀ ≤ A.card →
    ∀ d₁ dk : ℝ,
    (∃ p q : EuclideanSpace ℝ (Fin 2), p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ dist p q = d₁) →
    (∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → p ≠ q → d₁ ≤ dist p q) →
    (∃ p q : EuclideanSpace ℝ (Fin 2), p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ dist p q = dk) →
    (∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → dist p q ≤ dk) →
    (distFrequency A d₁ : ℝ) * (distFrequency A dk : ℝ) ≤
      (9 / 8 + ε) * (A.card : ℝ) ^ 2 :=
  sorry
