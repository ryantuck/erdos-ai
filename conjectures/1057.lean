import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Squarefree.Basic

open Finset Filter Real Classical

noncomputable section

/-!
# Erdős Problem #1057

Let C(x) count the number of Carmichael numbers in [1, x]. Is it true that
C(x) = x^{1-o(1)}?

A Carmichael number is a composite n > 1 such that a^n ≡ a (mod n) for all a.
By Korselt's criterion, this is equivalent to n being squarefree, composite,
and p - 1 ∣ n - 1 for all primes p ∣ n.

Alford, Granville, and Pomerance [AGP94] proved C(x) → ∞ and C(x) > x^{2/7}.
Harman [Ha08] improved the lower bound to C(x) > x^{0.33336704}.

Tags: number theory
-/

/-- A natural number n is a Carmichael number if n > 1, n is not prime,
    n is squarefree, and p - 1 ∣ n - 1 for every prime p dividing n.
    (This is Korselt's criterion.) -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- C(x) counts the number of Carmichael numbers in {1, ..., x}. -/
noncomputable def carmichaelCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => IsCarmichael n)).card

/--
Erdős Problem #1057 [Er56c]:

Is it true that C(x) = x^{1-o(1)}? That is, does log C(x) / log x → 1
as x → ∞?

This asks whether the Carmichael counting function grows almost as fast
as x itself, in the sense that the exponent approaches 1.
-/
theorem erdos_problem_1057 :
    Tendsto
      (fun x : ℕ => Real.log (carmichaelCount x : ℝ) / Real.log (x : ℝ))
      atTop (nhds 1) :=
  sorry

end
