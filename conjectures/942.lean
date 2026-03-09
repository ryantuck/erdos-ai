import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Set Filter Real

noncomputable section

/--
A positive integer m is **powerful** if for every prime p dividing m, p² also divides m.
-/
def IsPowerful (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

/--
h(n) counts the number of powerful integers in [n², (n+1)²).
-/
noncomputable def powerfulCount (n : ℕ) : ℕ :=
  Set.ncard {m : ℕ | n ^ 2 ≤ m ∧ m < (n + 1) ^ 2 ∧ IsPowerful m}

/--
Erdős Problem #942 [Er76d, p.35]:

Let h(n) count the number of powerful (if p∣m then p²∣m) integers in
[n², (n+1)²). Is there some constant c > 0 such that
  h(n) < (log n)^{c+o(1)}
and, for infinitely many n,
  h(n) > (log n)^{c-o(1)}?

The upper bound means: for every ε > 0, for all sufficiently large n,
  h(n) < (Real.log n)^{c+ε}.
The lower bound means: for every ε > 0, there exist infinitely many n with
  h(n) > (Real.log n)^{c-ε}.
-/
theorem erdos_problem_942 :
    ∃ c : ℝ, 0 < c ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          (powerfulCount n : ℝ) < rpow (Real.log n) (c + ε)) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
          (powerfulCount n : ℝ) > rpow (Real.log n) (c - ε)) :=
  sorry

end
