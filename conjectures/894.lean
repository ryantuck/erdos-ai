import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic

/--
A sequence `a : ℕ → ℕ` is lacunary if it is strictly increasing and there exists
some ε > 0 such that a(k+1) ≥ (1 + ε) · a(k) for all k.
-/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∃ ε : ℝ, ε > 0 ∧ ∀ k : ℕ, (a (k + 1) : ℝ) ≥ (1 + ε) * (a k : ℝ)

/--
Erdős Problem #894:

Let A = {n₁ < n₂ < ⋯} ⊂ ℕ be a lacunary sequence (there exists some ε > 0 with
n_{k+1} ≥ (1+ε)·n_k for all k).

Is it true that there must exist a finite colouring of ℕ with no monochromatic
solutions to a - b ∈ A?

Equivalently, does the Cayley graph on ℤ defined by a lacunary set have finite
chromatic number?

This was proved: the answer is yes. Katznelson observed it follows from the
solution to Problem 464 (on the Littlewood conjecture). The best quantitative
bound, due to Peres and Schlag, gives at most ≪ ε⁻¹ log(1/ε) colours.
-/
theorem erdos_problem_894 (a : ℕ → ℕ) (h : IsLacunary a) :
    ∃ (k : ℕ) (c : ℕ → Fin k),
      ∀ x y : ℕ, x > y → (∃ i, a i = x - y) → c x ≠ c y :=
  sorry
