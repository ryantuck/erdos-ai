import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/--
A sequence a : ℕ → ℕ is a Stanley sequence starting from {0, n} if:
1. a(0) = 0 and a(1) = n
2. a is strictly increasing
3. The image is 3-AP-free: no three indices i < j < k satisfy a(i) + a(k) = 2·a(j)
4. It is greedy: for every m between consecutive terms a(k) and a(k+1) (with k ≥ 1),
   adding m to {a(0), …, a(k)} would create a 3-term AP
-/
def IsStanleySeq (n : ℕ) (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = n ∧
  StrictMono a ∧
  (∀ i j k : ℕ, i < j → j < k → a i + a k ≠ 2 * a j) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, a k < m → m < a (k + 1) →
    ∃ i j : ℕ, i < j ∧ j ≤ k ∧ a i + m = 2 * a j)

/--
Erdős Problem #271 [ErGr80, p.22]:

Let A(n) = {a₀ < a₁ < ⋯} be the Stanley sequence defined by a₀ = 0, a₁ = n,
and for k ≥ 1, aₖ₊₁ is the least positive integer such that {a₀, …, aₖ₊₁}
contains no three-term arithmetic progression.

Can the aₖ be explicitly determined? How fast do they grow?

The Odlyzko–Stanley conjecture asserts that every such sequence eventually
satisfies either aₖ = Θ(k^{log₂ 3}) or aₖ = Θ(k² / log k). The first growth
rate is known for A(1), A(3ᵏ), and A(2·3ᵏ). No sequence with the second growth
rate has been proven, though computational evidence suggests A(4) may have this
growth. Moy proved the upper bound aₖ ≤ (k−1)(k+2)/2 + n for all k ≥ 0.
-/
theorem erdos_problem_271 (n : ℕ) (hn : 0 < n)
    (a : ℕ → ℕ) (ha : IsStanleySeq n a) :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C₁ * (k : ℝ) ^ (Real.log 3 / Real.log 2) ≤ (a k : ℝ) ∧
        (a k : ℝ) ≤ C₂ * (k : ℝ) ^ (Real.log 3 / Real.log 2))
    ∨
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C₁ * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (a k : ℝ) ∧
        (a k : ℝ) ≤ C₂ * (k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  sorry
