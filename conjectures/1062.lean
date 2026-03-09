import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Real.Irrational

/--
A subset A of {1,...,n} has a "divisor fork" if there exist three distinct
elements a, b, c ∈ A such that a ∣ b and a ∣ c.
-/
def HasDivisorFork (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∣ b ∧ a ∣ c

instance : DecidablePred HasDivisorFork := by
  intro A
  unfold HasDivisorFork
  infer_instance

/--
f(n) = the size of the largest subset A ⊆ {1,...,n} with no "divisor fork"
(no element dividing two other distinct elements).
-/
noncomputable def maxNoDivisorForkSize (n : ℕ) : ℕ :=
  Finset.sup
    ((Finset.Icc 1 n).powerset.filter (fun A => ¬ HasDivisorFork A))
    Finset.card

/--
Erdős Problem #1062 [Gu04]:

Let f(n) be the size of the largest subset A ⊆ {1,...,n} such that there are
no three distinct elements a, b, c ∈ A with a ∣ b and a ∣ c.

The limit lim f(n)/n exists and is irrational.

Lebensold [Le76] showed that for large n, 0.6725n ≤ f(n) ≤ 0.6736n.
-/
theorem erdos_problem_1062 :
    ∃ α : ℝ, Irrational α ∧
      Filter.Tendsto (fun n => (maxNoDivisorForkSize n : ℝ) / (n : ℝ))
        Filter.atTop (nhds α) :=
  sorry
