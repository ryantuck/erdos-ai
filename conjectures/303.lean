import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

/--
Erdős Problem #303 [ErGr80,p.37]:

Is it true that in any finite colouring of the positive integers there exists
a monochromatic solution to 1/a = 1/b + 1/c with distinct a, b, c?

This was proved by Brown and Rödl [BrRo91].
-/
theorem erdos_problem_303
    (k : ℕ) (hk : 0 < k)
    (f : ℕ → Fin k) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      f a = f b ∧ f b = f c ∧
      (1 : ℚ) / a = 1 / b + 1 / c :=
  sorry
