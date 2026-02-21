import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators Filter Real Classical

noncomputable section

/-!
# Erdős Problem #400

For any k ≥ 2, let g_k(n) denote the maximum value of (a₁ + ⋯ + aₖ) - n where
a₁, …, aₖ are natural numbers such that a₁!⋯aₖ! ∣ n!.

Can one show that ∑_{n ≤ x} g_k(n) ~ c_k · x · log x for some constant c_k?

Is it true that there is a constant c_k such that for almost all n < x we have
g_k(n) = c_k · log x + o(log x)?

Erdős and Graham note that g_k(n) ≪_k log n always, but the best possible
constant is unknown.
-/

/-- g_k(n) is the maximum of (a₁ + ⋯ + aₖ) - n over all k-tuples of natural numbers
    (a₁, …, aₖ) satisfying a₁!⋯aₖ! ∣ n!. -/
noncomputable def erdos400_g (k n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ a : Fin k → ℕ, (∏ i, (a i).factorial) ∣ n.factorial ∧
    s = (∑ i, a i) - n}

/--
Erdős Problem #400, Part 1 [ErGr80, p.77]:

For any k ≥ 2, there exists a constant c_k > 0 such that
∑_{n ≤ x} g_k(n) ~ c_k · x · log x.

Formalized as: the ratio (∑_{n=1}^{x} g_k(n)) / (x · log x) tends to c_k as x → ∞.
-/
theorem erdos_problem_400_part1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun x : ℕ =>
        (∑ n ∈ Finset.Icc 1 x, (erdos400_g k n : ℝ)) / ((x : ℝ) * Real.log (x : ℝ)))
        atTop (nhds c) :=
  sorry

/--
Erdős Problem #400, Part 2 [ErGr80, p.77]:

For any k ≥ 2, there exists a constant c_k such that for almost all n ≤ x,
g_k(n) = c_k · log x + o(log x).

Formalized as: for every ε > 0, the proportion of n ≤ x for which
|g_k(n) - c_k · log x| > ε · log x tends to 0 as x → ∞.
-/
theorem erdos_problem_400_part2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          |(erdos400_g k n : ℝ) - c * Real.log (x : ℝ)| >
            ε * Real.log (x : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) :=
  sorry

end
