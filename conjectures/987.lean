import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Field.Basic

noncomputable section

/-!
# Erdős Problem #987

Let x₁, x₂, … ∈ (0,1) be an infinite sequence and define
  A_k = limsup_{n → ∞} |∑_{j ≤ n} e(k·x_j)|
where e(x) = e^{2πix}.

Part 1: Is it true that limsup_{k → ∞} A_k = ∞?
Part 2: Is it possible for A_k = o(k)?

This is Problem 7.21 in Halberstam and Roth [Ha74], attributed to
Erdős [Er64b][Er65b].

Erdős remarks the analogous statement with sup_n in place of
limsup_n is 'easy to see'. Clunie [Cl67] proved A_k ≫ k^{1/2}
infinitely often, and showed there exist sequences with A_k ≤ k
for all k.
-/

/-- The exponential sum S(x, k, n) = ∑_{j < n} e^{2πi·k·x_j}. -/
noncomputable def exponentialSum (x : ℕ → ℝ) (k : ℕ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑((k : ℝ) * x j))

/--
Erdős Problem #987, Part 1 [Er64b][Er65b]:
For any sequence x₁, x₂, … ∈ (0,1), limsup_{k → ∞} A_k = ∞ where
A_k = limsup_{n → ∞} ‖∑_{j < n} e^{2πi·k·x_j}‖.

Equivalently: for every M, there exists k such that
‖∑_{j < n} e^{2πi·k·x_j}‖ ≥ M for infinitely many n.
-/
theorem erdos_problem_987_part1 :
    ∀ (x : ℕ → ℝ), (∀ j, x j ∈ Set.Ioo 0 1) →
    ∀ M : ℝ, ∃ k : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      M ≤ ‖exponentialSum x k n‖ :=
  sorry

/--
Erdős Problem #987, Part 2 [Er65b][Ha74]:
It is not possible for A_k = o(k). For any sequence x₁, x₂, … ∈ (0,1),
there exists c > 0 such that for infinitely many k,
‖∑_{j < n} e^{2πi·k·x_j}‖ ≥ c·k for infinitely many n.
-/
theorem erdos_problem_987_part2 :
    ∀ (x : ℕ → ℝ), (∀ j, x j ∈ Set.Ioo 0 1) →
    ∃ c : ℝ, 0 < c ∧ ∀ K₀ : ℕ, ∃ k : ℕ, K₀ ≤ k ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c * ↑k ≤ ‖exponentialSum x k n‖ :=
  sorry

end
