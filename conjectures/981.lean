import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter Real

noncomputable section

/-!
# Erdős Problem #981

Let ε > 0 and f_ε(p) be the smallest integer m such that
∑_{n ≤ N} (n/p) < ε·N for all N ≥ m, where (n/p) is the Legendre symbol.

Prove that ∑_{p < x} f_ε(p) ~ c_ε · x / log x for some c_ε > 0.

This was proved by Elliott [El69].
-/

/-- The partial sum of Legendre symbols (n/p) for n = 1, ..., N.
    We use the Jacobi symbol which coincides with the Legendre symbol for prime p. -/
def legendrePartialSum (p : ℕ) (N : ℕ) : ℤ :=
  (Finset.Icc 1 N).sum (fun n => jacobiSym (n : ℤ) p)

/-- f_ε(p): the smallest positive integer m such that for all N ≥ m,
    ∑_{n ≤ N} (n/p) < ε·N. Returns 0 if no such m exists. -/
noncomputable def fEpsilon (ε : ℝ) (p : ℕ) : ℕ :=
  sInf {m : ℕ | m ≥ 1 ∧ ∀ N : ℕ, N ≥ m → (legendrePartialSum p N : ℝ) < ε * (N : ℝ)}

/--
Erdős Problem #981 (proved by Elliott [El69]):

For every ε > 0, there exists c_ε > 0 such that
  ∑_{p < x, p prime} f_ε(p) ~ c_ε · x / log x.

Formulated as: the ratio ∑_{p < x} f_ε(p) / (x / log x) tends to c_ε.
-/
theorem erdos_problem_981 (ε : ℝ) (hε : ε > 0) :
    ∃ c : ℝ, c > 0 ∧
      Filter.Tendsto
        (fun x : ℕ =>
          (((Finset.range x).filter Nat.Prime).sum (fun p => fEpsilon ε p) : ℝ) /
            ((x : ℝ) / Real.log (x : ℝ)))
        Filter.atTop (nhds c) :=
  sorry

end
