import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Card

open Filter MeasureTheory Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/--
A sequence x : ℕ → ℝ is equidistributed in [0,1) if for every subinterval
[c, d) ⊆ [0,1), the proportion of indices n < N with x(n) ∈ [c,d)
converges to d - c as N → ∞.
-/
def IsEquidistributed492 (x : ℕ → ℝ) : Prop :=
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 →
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => c ≤ x n ∧ x n < d)).card : ℝ) / (N : ℝ))
      atTop (nhds (d - c))

/--
Given a strictly increasing sequence a : ℕ → ℕ, for x in some interval
[a(i), a(i+1)), returns the fractional position
(x - a(i)) / (a(i+1) - a(i)) ∈ [0,1).
Returns 0 if x is not in any such interval.
-/
def erdos492_f (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  if h : ∃ i : ℕ, (a i : ℝ) ≤ x ∧ x < (a (i + 1) : ℝ) then
    let i := Nat.find h
    (x - (a i : ℝ)) / ((a (i + 1) : ℝ) - (a i : ℝ))
  else 0

/--
Erdős Problem #492 (disproved by Schmidt [Sc69]):

Let A = {a₁ < a₂ < ⋯} ⊆ ℕ be infinite with a_{i+1}/a_i → 1.
For x ≥ a₁, define f(x) = (x - aᵢ)/(a_{i+1} - aᵢ) ∈ [0,1)
where aᵢ ≤ x < a_{i+1}. For example if A = ℕ then f(x) = {x} is
the usual fractional part operator.

The conjecture asked whether for almost all α, the sequence
f(αn) is uniformly distributed in [0,1). Schmidt showed this is false:
there exists such a sequence for which equidistribution fails on a
set of positive measure.
-/
theorem erdos_problem_492 :
    ∃ (a : ℕ → ℕ), StrictMono a ∧ (∀ i, 0 < a i) ∧
      Tendsto (fun i => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (nhds 1) ∧
      ¬(∀ᵐ α ∂(volume : Measure ℝ),
        IsEquidistributed492 (fun n => erdos492_f a (α * (n : ℝ)))) := by
  sorry

end
