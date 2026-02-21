import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #519

Let $z_1, \ldots, z_n \in \mathbb{C}$ with $z_1 = 1$. Must there exist an absolute
constant $c > 0$ such that
$$\max_{1 \leq k \leq n} \left| \sum_i z_i^k \right| > c?$$

A problem of Turán, who proved that this maximum is $\gg 1/n$. This was solved
by Atkinson [At61b], who showed that $c = 1/6$ suffices. This has been improved
by Biró, first to $c = 1/2$ [Bi94], and later to an absolute constant $c > 1/2$
[Bi00].
-/

/--
Erdős Problem #519 (Turán's power sum problem):

There exists an absolute constant c > 0 such that for any n ≥ 1 and any complex
numbers z₁, ..., zₙ with z₁ = 1,
  max_{1 ≤ k ≤ n} |∑ᵢ zᵢᵏ| > c.
-/
theorem erdos_problem_519 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ),
      z ⟨0, hn⟩ = 1 →
      ∃ k : Fin n, c < ‖∑ i : Fin n, z i ^ (k.val + 1)‖ :=
  sorry
