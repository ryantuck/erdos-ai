import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1171

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The multi-color ordinal partition relation α → (target₀, target_rest, ..., target_rest)²
    with (k+1) colors. For every (k+1)-coloring of pairs of ordinals below α, either
    there is a homogeneous set of order type target₀ for color 0, or there exists some
    color c > 0 with a homogeneous set of order type target_rest. -/
def OrdinalPartitionMulticolor (α : Ordinal) (k : ℕ) (target₀ target_rest : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Fin (k + 1),
    (∃ g : {x : Ordinal // x < target₀} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < target₀}, i < j → f (g i) (g j) = 0) ∨
    (∃ c : Fin (k + 1), 0 < c.val ∧
      ∃ g : {x : Ordinal // x < target_rest} → {x : Ordinal // x < α},
        StrictMono g ∧
        ∀ i j : {x : Ordinal // x < target_rest}, i < j → f (g i) (g j) = c)

/--
Erdős Problem #1171 [Va99, 7.84]:

Is it true that, for all finite k < ω,
  ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1}?

That is, for every (k+1)-coloring of pairs of ordinals below ω₁², either
there is a homogeneous set of order type ω₁·ω for the first color, or
there is a monochromatic triple for one of the remaining k colors.

Baumgartner [Ba89b] proved that, assuming a form of Martin's axiom,
ω₁·ω → (ω₁·ω, 3)².

Tags: set theory, ramsey theory
-/
theorem erdos_problem_1171 (k : ℕ) :
    OrdinalPartitionMulticolor (omega1 ^ 2) k (omega1 * omega0) 3 :=
  sorry

end Erdos1171
