import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Polynomial Finset BigOperators Filter

/-- The greatest prime factor of a natural number n, or 0 if n ≤ 1. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/-- The product of |f(m)| for m = 1, ..., n. -/
noncomputable def polyProduct (f : Polynomial ℤ) (n : ℕ) : ℕ :=
  ∏ m ∈ Finset.range n, (f.eval (↑(m + 1) : ℤ)).natAbs

/--
Erdős Problem #976 (Weak form):
Let f ∈ ℤ[x] be an irreducible polynomial of degree d ≥ 2. Let F_f(n) be the greatest
prime divisor of ∏_{m=1}^{n} f(m). Is it true that F_f(n) ≫ n^{1+c} for some c > 0?

Formalized as: there exist constants c > 0 and C > 0 such that for all sufficiently large n,
the greatest prime factor of ∏_{m=1}^{n} |f(m)| is at least C · n^{1+c}.
-/
theorem erdos_problem_976_conjecture
    (f : Polynomial ℤ) (hf_irr : Irreducible f) (hf_deg : 2 ≤ f.natDegree) :
    ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
      ∀ᶠ n in atTop,
        (greatestPrimeFactor (polyProduct f n) : ℝ) ≥ C * (n : ℝ) ^ (1 + c) :=
  sorry

/--
Erdős Problem #976 (Strong form):
Is it true that F_f(n) ≫ n^d where d = deg(f)?

Formalized as: there exists C > 0 such that for all sufficiently large n,
the greatest prime factor of ∏_{m=1}^{n} |f(m)| is at least C · n^d.
-/
theorem erdos_problem_976_strong_conjecture
    (f : Polynomial ℤ) (hf_irr : Irreducible f) (hf_deg : 2 ≤ f.natDegree) :
    ∃ (C : ℝ), C > 0 ∧
      ∀ᶠ n in atTop,
        (greatestPrimeFactor (polyProduct f n) : ℝ) ≥ C * (n : ℝ) ^ (f.natDegree) :=
  sorry
