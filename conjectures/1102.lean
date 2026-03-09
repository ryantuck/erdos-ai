import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Filter

namespace Erdos1102

/-!
# Erdős Problem #1102

We say that A ⊆ ℕ has property P if, for all n ≥ 1, there are only finitely many
a ∈ A such that n + a is squarefree.

We say that A has property Q if there are infinitely many n such that n + a is
squarefree for all a ∈ A with a < n.

How fast must sequences A = {a₁ < a₂ < ⋯} with properties P or Q increase?

Resolved by van Doorn and Tao [vDTa25]:
- Any sequence with property P has density 0, but density can go to 0 arbitrarily slowly.
- Any sequence with property Q has upper density at most 6/π², and this is achievable.

Tags: number theory
-/

/-- Property P: for all n ≥ 1, only finitely many a ∈ A satisfy "n + a is squarefree". -/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Set.Finite {a ∈ A | Squarefree (n + a)}

/-- Property Q: infinitely many n such that n + a is squarefree for all a ∈ A with a < n. -/
def HasPropertyQ (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}

/-- The counting function for a set S ⊆ ℕ up to N. -/
noncomputable def countingFn (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic N)

/-- The upper density of a set S ⊆ ℕ. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop

/-- The natural density of a set S ⊆ ℕ equals d if the ratio converges to d. -/
def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop (nhds d)

/-- Erdős Problem #1102, Part 1 (SOLVED) [Er81h, vDTa25]:

Any strictly increasing sequence with property P has density 0.
Equivalently, a(j)/j → ∞. -/
theorem density_zero_of_P (a : ℕ → ℕ) (ha : StrictMono a)
    (hP : HasPropertyP (Set.range a)) :
    Tendsto (fun j : ℕ => (a j : ℝ) / (j : ℝ)) atTop atTop :=
  sorry

/-- Erdős Problem #1102, Part 2 (SOLVED) [Er81h, vDTa25]:

For any function going to infinity, there exists a strictly increasing sequence
with property P that grows no faster than that function. That is, density can
go to 0 arbitrarily slowly. -/
theorem exists_sequence_with_P (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ HasPropertyP (Set.range a) ∧
      ∀ j : ℕ, (a j : ℝ) ≤ f j * (j : ℝ) :=
  sorry

/-- Erdős Problem #1102, Part 3 (SOLVED) [Er81h, vDTa25]:

Any set with property Q has upper density at most 6/π². -/
theorem upper_density_Q (A : Set ℕ) (hQ : HasPropertyQ A) :
    upperDensity A ≤ 6 / Real.pi ^ 2 :=
  sorry

/-- Erdős Problem #1102, Part 4 (SOLVED) [Er81h, vDTa25]:

There exists an infinite set with property Q and natural density equal to 6/π². -/
theorem exists_Q_with_max_density :
    ∃ A : Set ℕ, Set.Infinite A ∧ HasPropertyQ A ∧
      hasNaturalDensity A (6 / Real.pi ^ 2) :=
  sorry

end Erdos1102

end
