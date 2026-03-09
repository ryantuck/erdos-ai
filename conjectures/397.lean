import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Cofinite

open BigOperators Finset

/--
Erdős Problem #397 [ErGr80, p.77]:

Are there only finitely many solutions to
  ∏ᵢ C(2mᵢ, mᵢ) = ∏ⱼ C(2nⱼ, nⱼ)
with the mᵢ, nⱼ distinct?

DISPROVED by Somani (using ChatGPT). For any a ≥ 2, if c = 8a² + 8a + 1,
  C(2a,a) · C(4a+4,2a+2) · C(2c,c) = C(2a+2,a+1) · C(4a,2a) · C(2c+2,c+1).
This gives infinitely many solutions.

The formalization states the negation: there are infinitely many pairs of
disjoint finite sets (M, N) of naturals such that the products of central
binomial coefficients over M and N are equal.
-/
theorem erdos_problem_397 :
    Set.Infinite
      {p : Finset ℕ × Finset ℕ |
        Disjoint p.1 p.2 ∧
        p.1.Nonempty ∧
        p.2.Nonempty ∧
        ∏ m ∈ p.1, Nat.centralBinom m = ∏ n ∈ p.2, Nat.centralBinom n} :=
  sorry
