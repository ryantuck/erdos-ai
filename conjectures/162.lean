import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real

noncomputable section

/-!
# Erdős Problem #162

Let α > 0 and n ≥ 1. Let F(n, α) be the smallest threshold m such that there
exists a 2-colouring of the edges of K_n in which every induced subgraph H on
at least m vertices contains more than α * C(|H|, 2) edges of each colour.

Prove that for every fixed 0 ≤ α ≤ 1/2, as n → ∞,
  F(n, α) ∼ c_α log n
for some constant c_α > 0.

It is known (by the probabilistic method) that there exist c₁(α), c₂(α) > 0
such that c₁(α) log n < F(n, α) < c₂(α) log n.
-/

/-- A 2-colouring c of the edges (2-element subsets) of Fin n is α-balanced at
    threshold m if for every subset X ⊆ Fin n with |X| ≥ m, each colour class
    contains more than α * C(|X|, 2) many edges within X. -/
def IsEdgeBalanced (n m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card 2 : ℝ) <
        (((X.powersetCard 2).filter (fun S => c S = b)).card : ℝ)

/-- F(n, α) is the smallest threshold m such that there exists a 2-colouring
    of the edges of K_n that is α-balanced at threshold m. Equivalently, the
    largest k such that some 2-colouring makes every subset of size ≥ k
    balanced. -/
noncomputable def F_erdos162 (n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m α c }

/--
Erdős Conjecture (Problem #162) [Er90b, p.21]:

For every fixed 0 ≤ α ≤ 1/2, F(n, α) ∼ c_α log n for some constant c_α > 0.
That is, the ratio F(n, α) / log n converges to a positive constant c_α
as n → ∞.

This sharpens the known bound F(n, α) = Θ(log n) (established via the
probabilistic method) to an exact asymptotic with a well-defined constant.
-/
theorem erdos_problem_162 :
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          (c - ε) * Real.log (n : ℝ) ≤ (F_erdos162 n α : ℝ) ∧
          (F_erdos162 n α : ℝ) ≤ (c + ε) * Real.log (n : ℝ) :=
  sorry

end
