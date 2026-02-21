import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős Problem #202

Let n₁ < ⋯ < nᵣ ≤ N with associated aᵢ (mod nᵢ) such that the congruence
classes are disjoint (every integer is ≡ aᵢ (mod nᵢ) for at most one i).
How large can r be in terms of N?

Let f(N) denote the maximum such r. Erdős and Stein conjectured f(N) = o(N),
proved by Erdős and Szemerédi [ErSz68]. The exact asymptotics remain open.

The best known bounds, due to de la Bretèche, Ford, and Vandehey [BFV13], are:
  N / L(N)^{1+o(1)} < f(N) < N / L(N)^{√3/2+o(1)}
where L(N) = exp(√(log N · log log N)).

They conjecture the lower bound is the truth, i.e., f(N) = N / L(N)^{1+o(1)}.
-/

/-- A system of congruence classes with distinct positive moduli at most N is
    *pairwise disjoint* if no integer belongs to more than one class.
    Each element (n, a) represents the congruence class {x ∈ ℤ : x ≡ a (mod n)}. -/
def IsPairwiseDisjointSystem (S : Finset (ℕ × ℤ)) (N : ℕ) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ N) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    ∀ x : ℤ, ¬(x % (↑p.1 : ℤ) = p.2 % (↑p.1 : ℤ) ∧
               x % (↑q.1 : ℤ) = q.2 % (↑q.1 : ℤ)))

/--
Erdős Problem #202 (de la Bretèche–Ford–Vandehey conjecture) — OPEN
[Er61, Er65, Er65b, Er73, Er77c, ErGr80, Va99]:

The maximum number f(N) of pairwise disjoint congruence classes with distinct
moduli at most N satisfies f(N) ≤ N / L(N)^{1-ε} for every ε > 0 and all
sufficiently large N, where L(N) = exp(√(log N · log log N)).

Combined with the proved lower bound f(N) ≥ N / L(N)^{1+ε} [BFV13], this
gives the conjectured asymptotics f(N) = N / L(N)^{1+o(1)}.
-/
theorem erdos_problem_202 :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ N : ℕ in atTop,
    ∀ S : Finset (ℕ × ℤ),
    IsPairwiseDisjointSystem S N →
    (S.card : ℝ) ≤ (N : ℝ) /
      Real.exp ((1 - ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
  sorry
