import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Classical

/-!
# Erdős Problem #1103

Let A = {a₀ < a₁ < a₂ < ⋯} be an infinite sequence of positive integers such that
every element of the sumset A + A is squarefree. How fast must A grow?

Erdős notes there exists such a sequence which grows exponentially, but does not
expect such a sequence of polynomial growth to exist.

van Doorn and Tao [vDTa25] showed a_j > 0.24 j^{4/3} for all j, and that there
exists such a sequence with a_j < exp(5j / log j) for all large j.

Tags: number theory
-/

/--
Erdős Problem #1103 [Er81h, p.180]:

For any strictly increasing sequence a : ℕ → ℕ such that a(i) + a(j) is squarefree
for all i, j, the sequence must grow super-polynomially: for every C > 0, we have
a(j) > j^C for all sufficiently large j.
-/
theorem erdos_problem_1103
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (j : ℝ) ^ C < (a j : ℝ) :=
  sorry

end
