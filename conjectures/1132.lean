import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup

open Finset BigOperators Filter MeasureTheory

noncomputable section

namespace Erdos1132

/-!
# Erdős Problem #1132

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Let x₁, x₂, ... ∈ [-1,1] be an infinite sequence, and let
  L_n(x) = ∑_{1 ≤ k ≤ n} |l_k(x)|,
where each l_k(x) is defined with respect to x₁, ..., xₙ.

**Part 1:** Must there exist x ∈ (-1,1) such that
  L_n(x) > (2/π) log n - O(1)
for infinitely many n?

**Part 2:** Is it true that
  limsup_{n → ∞} L_n(x) / log n ≥ 2/π
for almost all x ∈ (-1,1)?

Bernstein [Be31] proved that the set of x ∈ (-1,1) for which the limsup
condition holds is everywhere dense.
-/

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: L_n(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The first n elements of an infinite sequence, viewed as Fin n → ℝ. -/
def firstN (seq : ℕ → ℝ) (n : ℕ) : Fin n → ℝ := fun i => seq i.val

/-- L_n(x): the Lebesgue function using the first n points of the sequence. -/
def L (seq : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  lebesgueFunction (firstN seq n) x

/-- A sequence is valid for interpolation: values in [-1,1] and pairwise distinct. -/
def ValidSeq (seq : ℕ → ℝ) : Prop :=
  Function.Injective seq ∧ ∀ i, seq i ∈ Set.Icc (-1 : ℝ) 1

/--
Erdős Problem #1132 (Part 1):

For any infinite sequence x₁, x₂, ... ∈ [-1,1] of distinct points, must there
exist x ∈ (-1,1) and a constant C such that L_n(x) > (2/π) log n - C for
infinitely many n?
-/
theorem erdos_problem_1132_part1 (seq : ℕ → ℝ) (hseq : ValidSeq seq) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
      ∃ᶠ n in atTop,
        L seq n x > (2 / Real.pi) * Real.log (n : ℝ) - C :=
  sorry

/--
Erdős Problem #1132 (Part 2):

For any infinite sequence x₁, x₂, ... ∈ [-1,1] of distinct points, is it true that
  limsup_{n → ∞} L_n(x) / log n ≥ 2/π
for almost all x ∈ (-1,1)?
-/
theorem erdos_problem_1132_part2 (seq : ℕ → ℝ) (hseq : ValidSeq seq) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
      Filter.limsup (fun n => L seq n x / Real.log (n : ℝ)) atTop ≥ 2 / Real.pi :=
  sorry

end Erdos1132
