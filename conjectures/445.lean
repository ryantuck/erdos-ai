import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq

open Real

/-!
# Erdős Problem #445

Is it true that, for any $c > 1/2$, if $p$ is a sufficiently large prime then,
for any $n \geq 0$, there exist $a, b \in (n, n + p^c)$ such that
$ab \equiv 1 \pmod{p}$?

Heilbronn (unpublished) proved this for $c$ sufficiently close to $1$.
Heath-Brown [He00] used Kloosterman sums to prove this for all $c > 3/4$.
-/

/-- Erdős Problem #445 (OPEN):
For any c > 1/2, if p is a sufficiently large prime then for any n ≥ 0
there exist a, b ∈ (n, n + p^c) with ab ≡ 1 (mod p). -/
theorem erdos_problem_445 (c : ℝ) (hc : c > 1 / 2) :
    ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
    ∀ n : ℕ, ∃ a b : ℕ,
    (n : ℝ) < (a : ℝ) ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    (n : ℝ) < (b : ℝ) ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p] :=
  sorry
