import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

open Polynomial

/--
Erdős Problem #477 [ErGr80,p.95]:

Is there a polynomial f : ℤ → ℤ of degree at least 2 and a set A ⊆ ℤ such
that for any n ∈ ℤ there is exactly one a ∈ A and b ∈ {f(m) : m ∈ ℤ} with
n = a + b?

Equivalently, does A + f(ℤ) form a perfect tiling of ℤ? Erdős and Graham
conjectured the answer is no.
-/
theorem erdos_problem_477 :
    ¬ ∃ (f : Polynomial ℤ) (A : Set ℤ),
      2 ≤ f.natDegree ∧
      ∀ n : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ (∃ m : ℤ, p.2 = f.eval m) ∧ n = p.1 + p.2 :=
  sorry
