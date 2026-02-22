import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

noncomputable section

/-!
# Erdős Problem #788

Let f(n) be maximal such that if B ⊂ (2n, 4n) ∩ ℕ there exists some
C ⊂ (n, 2n) ∩ ℕ such that c₁ + c₂ ∉ B for all c₁ ≠ c₂ ∈ C and
|C| + |B| ≥ f(n).

Estimate f(n). In particular is it true that f(n) ≤ n^{1/2+o(1)}?

A conjecture of Choi, who proved f(n) ≪ n^{3/4}. Adenwalla provided a
construction proving f(n) ≫ n^{1/2}. The bound f(n) ≪ (n log n)^{2/3} was
proved by Baltz, Schoen, and Srivastav. The work of Alon and Pham on random
Cayley graphs implies f(n) ≤ n^{3/5+o(1)}.

https://www.erdosproblems.com/788

Tags: additive combinatorics
-/

/-- f(n): the largest m such that for every B ⊆ (2n, 4n) ∩ ℕ, there exists
    C ⊆ (n, 2n) ∩ ℕ with c₁ + c₂ ∉ B for all distinct c₁, c₂ ∈ C and
    |C| + |B| ≥ m. -/
noncomputable def erdos788_f (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ B : Finset ℕ, B ⊆ Finset.Ioo (2 * n) (4 * n) →
    ∃ C : Finset ℕ, C ⊆ Finset.Ioo n (2 * n) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B) ∧
      C.card + B.card ≥ m}

/--
**Erdős Problem #788** — Conjectured upper bound:

f(n) ≤ n^{1/2+o(1)}, i.e., for every ε > 0 there exists N₀ such that
f(n) ≤ n^{1/2+ε} for all n ≥ N₀.
-/
theorem erdos_problem_788_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788_f n : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε) :=
  sorry

/--
**Erdős Problem #788** — Lower bound (Adenwalla):

f(n) ≫ n^{1/2}, i.e., there exists C > 0 such that f(n) ≥ C · n^{1/2}
for all sufficiently large n.
-/
theorem erdos_problem_788_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788_f n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
**Erdős Problem #788** — Upper bound (Alon–Pham [AlPh25]):

f(n) ≤ n^{3/5+o(1)}, i.e., for every ε > 0 there exists N₀ such that
f(n) ≤ n^{3/5+ε} for all n ≥ N₀.
-/
theorem erdos_problem_788_upper :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788_f n : ℝ) ≤ (n : ℝ) ^ (3 / 5 + ε) :=
  sorry

end
