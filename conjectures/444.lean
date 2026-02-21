import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finite.Defs

open Finset Filter BigOperators Classical

noncomputable section

/-!
# Erdős Problem #444

Let $A\subseteq\mathbb{N}$ be infinite and $d_A(n)$ count the number of $a\in A$
which divide $n$. Is it true that, for every $k$,
$$\limsup_{x\to \infty}  \frac{\max_{n<x}d_A(n)}{\left(\sum_{a\in A\cap[1,x)}\frac{1}{a}\right)^k}=\infty?$$

The answer is yes, proved by Erdős and Sárkőzy [ErSa80].
-/

/-- d_A(n): the number of elements of A that divide n. -/
def divisorCountIn (A : Set ℕ) (n : ℕ) : ℕ :=
  (n.divisors.filter (· ∈ A)).card

/-- The partial sum of reciprocals of elements of A in [1, x):
    ∑_{a ∈ A, 1 ≤ a < x} 1/a. -/
def reciprocalSum (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Ico 1 x).filter (· ∈ A), (1 : ℝ) / (a : ℝ)

/-- Erdős Problem #444 [ErGr80,p.88] (PROVED):

Let A ⊆ ℕ be infinite and d_A(n) count the number of a ∈ A dividing n.
For every k, limsup_{x→∞} max_{n<x} d_A(n) / (∑_{a∈A∩[1,x)} 1/a)^k = ∞.

Equivalently, for every M > 0, there are arbitrarily large x and some n < x
with d_A(n) > M · (∑_{a∈A∩[1,x)} 1/a)^k.

Proved by Erdős and Sárkőzy [ErSa80]. -/
theorem erdos_problem_444 (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    ∀ M : ℝ, 0 < M →
    ∃ᶠ x in atTop,
    ∃ n : ℕ, 1 ≤ n ∧ n < x ∧
    M * (reciprocalSum A x) ^ k < (divisorCountIn A n : ℝ) :=
  sorry

end
