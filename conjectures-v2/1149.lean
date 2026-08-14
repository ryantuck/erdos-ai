import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Defs

open Finset Filter Real Classical

noncomputable section

/-!
# Erdős Problem #1149

Let α > 0 be a real number, not an integer. The density of integers n ≥ 1
for which gcd(n, ⌊n^α⌋) = 1 is 6/π².

Verbatim source statement (erdosproblems.com/1149, page edition 23 January 2026,
accessed 2026-02-23): "Let $\alpha>0$ be a real number, not an integer. The density
of integers $n\geq 1$ for which $(n,\lfloor n^\alpha\rfloor)=1$ is $6/\pi^2$."

Status: PROVED ("This has been solved in the affirmative."). The site's remarks:
"This is true, and was proved by Bergelson and Richter [BeRi17]."

References (stubs; journal/volume/pages not recoverable offline — see review):

[Va99] Vardi, I., *Computational Recreations in Mathematica* (1999), Problem 1.34.
(Problem source key on the page: [Va99,1.34].)

[BeRi17] Bergelson, V. and Richter, F. K., *Dynamical generalizations of the prime
number theorem and disjointness of additive and multiplicative semigroup actions*
(2017).

Tags: number theory
-/

/--
Erdős Problem #1149 [Va99,1.34]:

Let α > 0 be a real number, not an integer. The natural density of integers
n ≥ 1 for which gcd(n, ⌊n^α⌋) = 1 equals 6/π².

The constant 6/π² = 1/ζ(2) is the "probability" that two random integers
are coprime, so this says n and ⌊n^α⌋ behave like independent random integers
with respect to coprimality when α is not an integer.

This is true, and was proved by Bergelson and Richter [BeRi17].
-/
theorem erdos_problem_1149 (α : ℝ) (hα_pos : 0 < α) (hα_not_int : ∀ k : ℤ, (k : ℝ) ≠ α) :
    Tendsto (fun x : ℕ =>
      (((Icc 1 x).filter (fun n =>
        Nat.Coprime n (⌊(n : ℝ) ^ α⌋₊))).card : ℝ) / (x : ℝ))
      atTop (nhds (6 / Real.pi ^ 2)) :=
  sorry

end
