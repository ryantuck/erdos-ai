import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

open Filter Asymptotics Classical

/--
The additive representation function r_A(n) = (1_A * 1_A)(n) counts the number of ordered
pairs (a, b) with a, b ∈ A and a + b = n. This is the Dirichlet convolution of the indicator
function 1_A with itself, evaluated at n.
-/
noncomputable def addRepFun (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

/--
Erdős Problem #29:
There exists a set A ⊆ ℕ such that:
1. A is an additive basis of order 2: every natural number is a sum of two elements of A
   (i.e., A + A = ℕ), and
2. The additive representation function 1_A * 1_A(n) grows sub-polynomially:
   1_A * 1_A(n) = o(n^ε) for every ε > 0.

The existence of such a set was first proved by Erdős using probabilistic methods
(answering a question of Sidon from 1932). An explicit construction was given by
Jain, Pham, Sawhney, and Zakharov (2024).
-/
theorem erdos_problem_29 :
    ∃ A : Set ℕ,
      (∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ => (addRepFun A n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ε) :=
  sorry
