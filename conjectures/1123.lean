import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Order.Basic

noncomputable section

open Filter Finset Classical BigOperators

/-- The natural (asymptotic) density of a set A ⊆ ℕ is zero if
    |A ∩ {0,...,n}| / (n+1) → 0 as n → ∞. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    ((Finset.filter (· ∈ A) (Finset.range (n + 1))).card : ℝ) / ((n : ℝ) + 1))
    atTop (nhds 0)

/-- The logarithmic density of a set A ⊆ ℕ is zero if
    (1/log n) · Σ_{k ∈ A, 1 ≤ k ≤ n} 1/k → 0 as n → ∞. -/
def HasLogDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    (∑ k ∈ Finset.filter (· ∈ A) (Finset.Icc 1 n), (1 : ℝ) / (k : ℝ)) /
    Real.log (n : ℝ))
    atTop (nhds 0)

/-- Two sets of naturals are equivalent mod natural-density-0 sets
    iff their symmetric difference has natural density zero. -/
def NatDensityEquiv (A B : Set ℕ) : Prop :=
  HasNaturalDensityZero (symmDiff A B)

/-- Two sets of naturals are equivalent mod log-density-0 sets
    iff their symmetric difference has logarithmic density zero. -/
def LogDensityEquiv (A B : Set ℕ) : Prop :=
  HasLogDensityZero (symmDiff A B)

/-- The equivalence relation on Set ℕ given by natural density zero. -/
def natDensitySetoid : Setoid (Set ℕ) where
  r := NatDensityEquiv
  iseqv := sorry

/-- The equivalence relation on Set ℕ given by logarithmic density zero. -/
def logDensitySetoid : Setoid (Set ℕ) where
  r := LogDensityEquiv
  iseqv := sorry

/-- B₁: the Boolean algebra of sets of integers modulo sets of natural density 0. -/
def BoolAlgModNatDensity : Type := Quotient natDensitySetoid

/-- B₂: the Boolean algebra of sets of integers modulo sets of logarithmic density 0. -/
def BoolAlgModLogDensity : Type := Quotient logDensitySetoid

instance : BooleanAlgebra BoolAlgModNatDensity := sorry
instance : BooleanAlgebra BoolAlgModLogDensity := sorry

/--
Erdős Problem #1123:
Let B₁ be the Boolean algebra of sets of integers modulo sets of density 0
and let B₂ be the Boolean algebra of sets modulo sets of logarithmic density 0.
Prove that B₁ and B₂ are not isomorphic.

Note: This is independent of ZFC. Just and Krawczyk [JuKr84] proved under the
continuum hypothesis that these two algebras ARE isomorphic.
-/
theorem erdos_problem_1123 :
    ¬ Nonempty (BoolAlgModNatDensity ≃o BoolAlgModLogDensity) :=
  sorry

end
