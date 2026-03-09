import Mathlib.Data.Finite.Defs

/--
A function f : ℕ → ℕ satisfies the Hofstadter recurrence if f(1) = f(2) = 1
and for all n ≥ 3, f(n) = f(n - f(n-1)) + f(n - f(n-2)).
-/
def IsHofstadterSeq (f : ℕ → ℕ) : Prop :=
  f 1 = 1 ∧ f 2 = 1 ∧
    ∀ n, n ≥ 3 → f n = f (n - f (n - 1)) + f (n - f (n - 2))

/--
Erdős Problem #422 [ErGr80]:

Let f(1) = f(2) = 1 and for n > 2 define f(n) = f(n - f(n-1)) + f(n - f(n-2)).
Does f(n) miss infinitely many integers?

Asked by Hofstadter. The sequence begins 1, 1, 2, 3, 3, 4, … and is A005185 in
the OEIS. It is not even known whether f(n) is well-defined for all n.

This formalization assumes f is a total function satisfying the recurrence and
conjectures that the range of f omits infinitely many natural numbers.
-/
theorem erdos_problem_422
    (f : ℕ → ℕ)
    (hf : IsHofstadterSeq f) :
    Set.Infinite {m : ℕ | m ≥ 1 ∧ ∀ n, f n ≠ m} :=
  sorry
