import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

/-!
# Erdős Problem #187

Find the best function f(d) such that, in any 2-colouring of the integers,
at least one colour class contains an arithmetic progression with common
difference d of length f(d) for infinitely many d.

Originally asked by Cohen. Erdős observed that colouring according to whether
{√2 · n} < 1/2 or not implies f(d) ≪ d (using the fact that ‖√2 · q‖ ≫ 1/q
for all q, where ‖x‖ is the distance to the nearest integer). Beck [Be80]
improved this using the probabilistic method, constructing a colouring that
shows f(d) ≤ (1+o(1))log₂ d. Van der Waerden's theorem implies f(d) → ∞
is necessary.
-/

/-- A 2-colouring χ : ℤ → Bool has a monochromatic arithmetic progression of
    length k with common difference d: there exist a starting point a ∈ ℤ and
    a colour c such that χ(a + i·d) = c for all 0 ≤ i < k. -/
def hasMonoAP (χ : ℤ → Bool) (d : ℕ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ c : Bool, ∀ i : ℕ, i < k → χ (a + ↑i * ↑d) = c

/--
Erdős Problem #187 [Er73, ErGr79, ErGr80]:

There exists an absolute constant c > 0 such that, for any 2-colouring
χ : ℤ → Bool, there are infinitely many positive integers d for which χ
has a monochromatic arithmetic progression with common difference d and
length at least c · log(d).

The upper bound direction is known: Beck [Be80] showed there exists a
2-colouring such that the longest monochromatic AP with common difference
d has length at most (1+o(1)) · log₂(d). So the best f(d) is Θ(log d)
if this conjecture holds.
-/
theorem erdos_problem_187 :
    ∃ c : ℝ, 0 < c ∧
    ∀ χ : ℤ → Bool,
    ∀ N : ℕ, ∃ d : ℕ, N < d ∧
      ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ hasMonoAP χ d k :=
  sorry

end
