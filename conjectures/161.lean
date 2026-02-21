import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

noncomputable section

/-!
# Erdős Problem #161

Let α ∈ [0, 1/2) and n, t ≥ 1. Let F^{(t)}(n, α) be the smallest m such that
we can 2-colour the edges of the complete t-uniform hypergraph on n vertices
such that if X ⊆ [n] with |X| ≥ m then there are at least α * C(|X|, t) many
t-subsets of X of each colour.

For fixed n, t as we change α from 0 to 1/2 does F^{(t)}(n, α) increase
continuously or are there jumps? Only one jump?

Erdős guessed that the jump occurs all in one step at α = 0: for any
fixed α > 0, F^{(t)}(n, α) grows at most polynomially in log n, whereas
F^{(t)}(n, 0) ≈ log_{t-1}(n) grows much more slowly (iterated logarithm).

For t = 3, this was proved by Conlon, Fox, and Sudakov [CFS11]:
F^{(3)}(n, α) ≤ C_α * √(log n) for any fixed α > 0.
-/

/-- A 2-colouring c of the t-element subsets of Fin n is α-balanced at
    threshold m if for every subset X ⊆ Fin n with |X| ≥ m, each colour class
    contains at least α * C(|X|, t) many t-element subsets of X. -/
def IsBalancedColouring (n t m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card t : ℝ) ≤
        (((X.powersetCard t).filter (fun S => c S = b)).card : ℝ)

/-- F^{(t)}(n, α) is the smallest m such that there exists a 2-colouring of the
    t-element subsets of [n] that is α-balanced at threshold m. -/
noncomputable def F_balanced (t n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsBalancedColouring n t m α c }

/--
Erdős Conjecture (Problem #161) [Er90b, p.21]:

For any t ≥ 2 and 0 < α < 1/2, the function F^{(t)}(n, α) is bounded by a
polynomial in log n. Specifically, there exist constants C > 0 and D > 0
(depending on t and α) such that F^{(t)}(n, α) ≤ C * (log n)^D for all
sufficiently large n.

This captures Erdős's conjecture that "the jump occurs all in one step at 0":
for α > 0, F^{(t)}(n, α) grows polynomially in log n, contrasting with the
much slower iterated-logarithm growth F^{(t)}(n, 0) ≈ log_{t-1}(n).
-/
theorem erdos_problem_161 :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ D : ℝ, 0 < D ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (F_balanced t n α : ℝ) ≤ C * (Real.log (n : ℝ)) ^ D :=
  sorry

end
