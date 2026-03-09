import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

noncomputable section

/-- Area of a triangle with vertices p₁, p₂, p₃ via the cross product formula. -/
def triangleArea352 (p₁ p₂ p₃ : ℝ × ℝ) : ℝ :=
  |(p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2)| / 2

/--
Erdős Problem #352 [Er78d,p.122] [Er81b,p.30] [Er83d,p.323] [Va99,2.47]:

Is there some c > 0 such that every measurable A ⊆ ℝ² of measure ≥ c contains
the vertices of a triangle of area 1?

Erdős proved this when A has infinite measure, or when A is unbounded with
positive measure. He speculated that c = 4π/√27 ≈ 2.418 works, which would be
best possible (as witnessed by a circle of radius < 2·3^{-3/4}).

Freiling and Mauldin proved that if A has outer measure > 4π/√27 then A contains
vertices of a triangle with area > 1, which also settles the conjecture when A
is a compact convex set.
-/
theorem erdos_problem_352 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : Set (ℝ × ℝ)),
        MeasurableSet A →
        c ≤ (volume A).toReal →
        ∃ p₁ p₂ p₃ : ℝ × ℝ,
          p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧
          triangleArea352 p₁ p₂ p₃ = 1 :=
  sorry

end
