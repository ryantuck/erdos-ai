import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

open BigOperators Finset Real

/-!
# Erdős Problem #510

Chowla's cosine problem. If A ⊂ ℤ is a finite set of size N, is there
some absolute constant c > 0 and θ such that
  ∑ n in A, cos(n * θ) < -c * N^(1/2)?

Ruzsa [Ru04] proved an upper bound of -exp(O(√(log N))), improving on
Bourgain [Bo86]. Polynomial bounds were proved independently by Bedert
[Be25c] and Jin–Milojević–Tomon–Zhang [JMTZ25]. Bedert's method gives
the bound -c * N^(1/7) for some c > 0.

The example A = B - B, where B is a Sidon set, shows that N^(1/2) would
be the best possible.
-/

/--
Erdős Problem #510 [Er61,p.248]:

There exists an absolute constant c > 0 such that for every finite set
A ⊂ ℤ of size N, there exists θ ∈ ℝ with
  ∑ n in A, cos(n * θ) < -c * √N.
-/
theorem erdos_problem_510 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : Finset ℤ), A.Nonempty →
        ∃ θ : ℝ, ∑ n ∈ A, Real.cos (n * θ) < -c * Real.sqrt A.card :=
  sorry
