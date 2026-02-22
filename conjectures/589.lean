import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #589

Let g(n) be maximal such that in any set of n points in ℝ² with no four
points on a line there exists a subset of g(n) points with no three points
on a line. Estimate g(n).

The trivial greedy algorithm gives g(n) ≫ n^{1/2}. Füredi [Fu91b] proved
  n^{1/2} log n ≪ g(n) = o(n).
Balogh and Solymosi [BaSo18] improved the upper bound to
  g(n) ≪ n^{5/6+o(1)}.

https://www.erdosproblems.com/589
-/

/-- A finite set of points in ℝ² has at most `k` points on any affine line.
    Equivalently, no `k + 1` points of `S` are collinear (lie on a common
    line `{p | a * p 0 + b * p 1 = c}` for some `(a, b) ≠ (0, 0)`). -/
def atMostKOnAnyLine (k : ℕ) (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ T : Finset (Fin 2 → ℝ), T ⊆ S → T.card = k + 1 →
    ¬∃ (a b c : ℝ), (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ p : Fin 2 → ℝ, p ∈ T → a * p 0 + b * p 1 = c

/-- `erdos589_g n` is the largest `m` such that every set of `n` points in ℝ²
    with no four on a line contains a subset of at least `m` points with no
    three on a line. -/
noncomputable def erdos589_g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ S : Finset (Fin 2 → ℝ),
    S.card = n → atMostKOnAnyLine 3 S →
    ∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ m ≤ T.card ∧ atMostKOnAnyLine 2 T}

/--
Erdős Problem #589 (lower bound, Füredi [Fu91b]):

There exists a constant `C > 0` such that for all sufficiently large `n`,
  `erdos589_g n ≥ C * √n * log n`.
-/
theorem erdos_problem_589_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos589_g n : ℝ) ≥ C * Real.sqrt (↑n) * Real.log (↑n) :=
  sorry

/--
Erdős Problem #589 (upper bound, Balogh-Solymosi [BaSo18]):

For all `ε > 0`, there exists `C > 0` such that for all sufficiently large `n`,
  `erdos589_g n ≤ C * n ^ (5/6 + ε)`.
-/
theorem erdos_problem_589_upper (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos589_g n : ℝ) ≤ C * (↑n : ℝ) ^ ((5 : ℝ) / 6 + ε) :=
  sorry

end
