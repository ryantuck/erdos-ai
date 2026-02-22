import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

noncomputable section

open Real Finset

/-!
# Erdős Problem #829

Let A ⊂ ℕ be the set of cubes. Is it true that
  1_A ∗ 1_A(n) ≪ (log n)^{O(1)}?

Here 1_A ∗ 1_A(n) counts the number of representations of n as a sum of two
positive cubes, i.e., the number of pairs (a, b) with a³ + b³ = n.

Mordell proved that lim sup 1_A ∗ 1_A(n) = ∞. Mahler [Ma35b] proved
1_A ∗ 1_A(n) ≫ (log n)^{1/4} for infinitely many n. Stewart [St08] improved
this to 1_A ∗ 1_A(n) ≫ (log n)^{11/13}.

Tags: number theory
-/

/-- The number of representations of n as a sum of two positive cubes:
    |{(a, b) ∈ ℕ × ℕ : a ≥ 1 ∧ b ≥ 1 ∧ a³ + b³ = n}|. -/
def sumOfTwoCubesRepr (n : ℕ) : ℕ :=
  ((Finset.range n).product (Finset.range n)).filter
    (fun p => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 ^ 3 + p.2 ^ 3 = n) |>.card

/--
**Erdős Problem #829** [Er83]:

The number of representations of n as a sum of two positive cubes is bounded
by a polynomial in log n. That is, there exist constants C > 0 and k > 0
such that for all sufficiently large n,
  sumOfTwoCubesRepr(n) ≤ C · (log n)^k.
-/
theorem erdos_problem_829 :
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℝ, k > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (sumOfTwoCubesRepr n : ℝ) ≤ C * (Real.log n) ^ k :=
  sorry

end
