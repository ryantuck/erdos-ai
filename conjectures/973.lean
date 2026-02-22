import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #973

Does there exist a constant $C > 1$ such that, for every $n \geq 2$, there
exists a sequence $z_i \in \mathbb{C}$ with $z_1 = 1$ and $|z_i| \geq 1$ for
all $1 \leq i \leq n$ with
$$\max_{2 \leq k \leq n+1} \left| \sum_{1 \leq i \leq n} z_i^k \right| < C^{-n}?$$

A problem of Erdős [Er65b, p.213]. See also [519].
-/

/--
Erdős Problem #973 [Er65b, p.213]:

There exists a constant C > 1 such that for every n ≥ 2, there exists a
sequence z₁, ..., zₙ ∈ ℂ with z₁ = 1 and ‖zᵢ‖ ≥ 1 for all i, such that
for all k with 2 ≤ k ≤ n + 1,
  ‖∑ᵢ zᵢᵏ‖ < C⁻¹ⁿ.
-/
theorem erdos_problem_973 :
    ∃ C : ℝ, C > 1 ∧
    ∀ (n : ℕ) (hn : n ≥ 2),
    ∃ z : Fin n → ℂ,
      z ⟨0, by omega⟩ = 1 ∧
      (∀ i, 1 ≤ ‖z i‖) ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n + 1 →
        ‖∑ i : Fin n, z i ^ k‖ < C⁻¹ ^ n :=
  sorry
