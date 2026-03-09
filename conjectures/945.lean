import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

/--
The number of divisors of a natural number.
-/
def tau (m : ℕ) : ℕ := m.divisors.card

/--
F(x) is the maximal k such that there exist consecutive integers
n+1, ..., n+k ≤ x with τ(n+1), ..., τ(n+k) all distinct.
-/
noncomputable def F (x : ℕ) : ℕ :=
  Finset.sup (Finset.range x) fun n =>
    Finset.sup (Finset.range x) fun k =>
      if n + k ≤ x ∧
         (∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
           i ≠ j → tau (n + 1 + i) ≠ tau (n + 1 + j))
      then k
      else 0

/--
Erdős Problem #945 [ErMi52, Er85e]:

Let F(x) be the maximal k such that there exist n+1, ..., n+k ≤ x with
τ(n+1), ..., τ(n+k) all distinct (where τ(m) counts the divisors of m).

Is it true that F(x) ≤ (log x)^C for some constant C > 0? In other words,
is there a constant C > 0 such that, for all large x, every interval
[x, x + (log x)^C] contains two integers with the same number of divisors?

Erdős and Mirsky proved that
  (log x)^{1/2} / log log x ≪ F(x) ≪ exp(O((log x)^{1/2} / log log x)).

Beker improved the upper bound to F(x) ≪ exp(O((log x)^{1/3 + o(1)})).
-/
theorem erdos_problem_945 :
    ∃ C : ℝ, 0 < C ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
        (F x : ℝ) ≤ (Real.log (x : ℝ)) ^ C :=
  sorry
