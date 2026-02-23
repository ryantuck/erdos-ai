import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

open Polynomial Finset Set

noncomputable section

namespace Erdos1133

/-!
# Erdős Problem #1133

Let C > 0. There exists ε > 0 such that if n is sufficiently large the following holds.

For any x₁, ..., xₙ ∈ [-1,1] there exist y₁, ..., yₙ ∈ [-1,1] such that, if P is a
polynomial of degree m < (1+ε)n with P(xᵢ) = yᵢ for at least (1-ε)n many 1 ≤ i ≤ n,
then max_{x ∈ [-1,1]} |P(x)| > C.

Erdős proved that, for any C > 0, there exists ε > 0 such that if n is sufficiently
large and m = ⌊(1+ε)n⌋ then for any x₁, ..., xₘ ∈ [-1,1] there is a polynomial P of
degree n such that |P(xᵢ)| ≤ 1 for 1 ≤ i ≤ m and max_{x ∈ [-1,1]} |P(x)| > C.
The conjectured statement would also imply this, but Erdős said he could not even prove
it for m = n.
-/

/--
Erdős Problem #1133:

Let C > 0. There exists ε > 0 such that for sufficiently large n, for any
x₁, ..., xₙ ∈ [-1,1] there exist y₁, ..., yₙ ∈ [-1,1] such that any polynomial P
of degree < (1+ε)n that agrees with yᵢ at xᵢ for at least (1-ε)n indices i
must satisfy max_{x ∈ [-1,1]} |P(x)| > C.
-/
theorem erdos_problem_1133 :
    ∀ C : ℝ, C > 0 →
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (-1 : ℝ) 1) →
    ∃ y : Fin n → ℝ, (∀ i, y i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ P : Polynomial ℝ, (P.natDegree : ℝ) < (1 + ε) * n →
    ((univ.filter (fun i : Fin n => P.eval (x i) = y i)).card : ℝ) ≥ (1 - ε) * n →
    ∃ t ∈ Icc (-1 : ℝ) 1, |P.eval t| > C :=
  sorry

end Erdos1133
