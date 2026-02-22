import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Real.Irrational

open Nat Finset Filter

noncomputable section

/-!
# Erdős Problem #1062

Let f(n) be the size of the largest subset A ⊆ {1,...,n} such that there are no
three distinct elements a, b, c ∈ A with a ∣ b and a ∣ c (i.e. no element
divides two other distinct elements). Such a set is called "fork-free".

How large can f(n) be? Is lim f(n)/n irrational?

The example [m+1, 3m+2] shows f(n) ≥ ⌈2n/3⌉. Lebensold [Le76] showed that
for large n, 0.6725n ≤ f(n) ≤ 0.6736n.

This is problem B24 in Guy's collection [Gu04].
-/

/-- A subset A of positive integers is fork-free if no element of A divides
    two other distinct elements of A. Equivalently, there are no three distinct
    elements a, b, c ∈ A with a ∣ b and a ∣ c. -/
def IsForkFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → a ∣ b → a ∣ c → False

/-- f(n): the maximum size of a fork-free subset of {1,...,n}. -/
noncomputable def erdos1062_f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ IsForkFree A ∧ A.card = k}

/--
Erdős Problem #1062 [Gu04]:

Is lim_{n → ∞} f(n)/n irrational, where f(n) is the maximum size of a
fork-free subset of {1,...,n}?

Formulated as: the limit exists and is irrational.
-/
theorem erdos_problem_1062 :
    ∃ L : ℝ, Irrational L ∧
      Tendsto (fun n : ℕ => (erdos1062_f n : ℝ) / (n : ℝ))
        atTop (nhds L) :=
  sorry

end
