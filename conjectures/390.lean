import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

noncomputable section

/--
The minimal largest factor `m` such that `n! = a₁ ⬝ ⋯ ⬝ aₖ` with `n < a₁ < ⋯ < aₖ = m`.
That is, `f(n)` is the smallest `m` for which `n!` can be written as a product of distinct
integers all greater than `n`, the largest of which is `m`.
-/
noncomputable def erdos390_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (S : Finset ℕ),
    (∀ a ∈ S, n < a) ∧
    m ∈ S ∧
    (∀ a ∈ S, a ≤ m) ∧
    S.prod id = n ! }

/--
Erdős Problem #390 [ErGr80, EGS82]:

Let f(n) be the minimal m such that n! = a₁ ⬝ ⋯ ⬝ aₖ with n < a₁ < ⋯ < aₖ = m.
Is there a constant c such that f(n) - 2n ~ c · n / log n?

Erdős, Guy, and Selfridge [EGS82] have shown that f(n) - 2n = Θ(n / log n).
-/
theorem erdos_problem_390 :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        |((erdos390_f n : ℝ) - 2 * n) / (n / Real.log n) - c| < ε :=
  sorry

end
