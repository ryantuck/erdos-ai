import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

noncomputable section

/--
The number of divisors of n that lie in the open interval (√n, √n + n^{1/2 - ε}).
-/
def divisorsInInterval (n : ℕ) (ε : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d =>
    (n : ℝ) ^ ((1 : ℝ) / 2) < (d : ℝ) ∧
    (d : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2 - ε))

/--
Erdős Problem #886 [ErRo97, Er98]:

Let ε > 0. Is it true that, for all large n, the number of divisors of n in
(n^{1/2}, n^{1/2} + n^{1/2 - ε}) is O_ε(1)?

That is, for every ε > 0, there exist constants C and N₀ such that for all
n ≥ N₀, the number of divisors of n in that interval is at most C.

Erdős attributes this conjecture to Ruzsa. Erdős and Rosenfeld proved that
there are infinitely many n with four divisors in (n^{1/2}, n^{1/2} + 16n^{1/4}),
and that for any constant C > 0, all large n have at most 1 + C² divisors in
[n^{1/2}, n^{1/2} + Cn^{1/4}].
-/
theorem erdos_problem_886 :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℕ, ∃ N₀ : ℕ,
        ∀ n : ℕ, N₀ ≤ n →
          (divisorsInInterval n ε).card ≤ C :=
  sorry

end
