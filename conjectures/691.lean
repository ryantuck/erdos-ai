import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #691

Given $A ⊆ ℕ$, let $M_A = \{n ≥ 1 : a ∣ n \text{ for some } a ∈ A\}$ be the set
of multiples of $A$. Find a necessary and sufficient condition on $A$ for $M_A$
to have density $1$.

A sequence $A$ for which $M_A$ has density $1$ is called a Behrend sequence.

For pairwise coprime sets of integers (all ≥ 2), a necessary and sufficient
condition is $∑_{a ∈ A} 1/a = ∞$.

The general characterization remains open.

Reference: [Er79e, p.77]
https://www.erdosproblems.com/691
-/

/-- Count of integers m ∈ {1, ..., N} such that some element of A divides m. -/
noncomputable def countMultiples (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => ∃ a ∈ A, a ∣ (n + 1))).card

/-- A set A ⊆ ℕ is a Behrend sequence if the set of multiples of A has
    natural density 1, i.e., |M_A ∩ {1,...,N}| / N → 1 as N → ∞. -/
def IsBehrend (A : Set ℕ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (countMultiples A (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
    atTop (nhds 1)

/-- A set of natural numbers is pairwise coprime. -/
def SetPairwiseCoprime (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b

/-- The sum of reciprocals of elements of A diverges: for every bound C > 0,
    some finite subset of A achieves a reciprocal sum exceeding C. -/
def ReciprocalSumDiverges (A : Set ℕ) : Prop :=
  ∀ C : ℝ, C > 0 → ∃ F : Finset ℕ, (∀ a ∈ F, a ∈ A) ∧
    C < ∑ a ∈ F, (1 : ℝ) / (a : ℝ)

/--
Erdős Problem #691 (pairwise coprime case):
If A is a set of pairwise coprime integers (all ≥ 2), then A is a Behrend
sequence if and only if the sum of reciprocals ∑_{a ∈ A} 1/a diverges.
-/
theorem erdos_problem_691 (A : Set ℕ) (hA : ∀ a ∈ A, a ≥ 2)
    (hCoprime : SetPairwiseCoprime A) :
    IsBehrend A ↔ ReciprocalSumDiverges A :=
  sorry

end
