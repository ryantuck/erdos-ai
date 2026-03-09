import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

/--
Erdős Problem #324 [ErGr80, p.53]:

Does there exist a polynomial f(x) ∈ ℤ[x] such that all the sums f(a) + f(b)
with a < b nonnegative integers are distinct?

Erdős and Graham describe this problem as 'very annoying'. Probably f(x) = x⁵
should work. The Lander–Parkin–Selfridge conjecture would imply that f(x) = xⁿ
has this property for all n ≥ 5.
-/
theorem erdos_problem_324 :
    ∃ f : ℤ[X],
      ∀ a b c d : ℕ, a < b → c < d →
        f.eval (a : ℤ) + f.eval (b : ℤ) = f.eval (c : ℤ) + f.eval (d : ℤ) →
        a = c ∧ b = d :=
  sorry
