import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1169

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The ordinal partition relation α → (β, γ)² for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below α, there is either
    a homogeneous set of order type β in color 0, or a homogeneous set of
    order type γ in color 1. Formalized via strictly monotone embeddings:
    a subset of order type β corresponds to a strictly monotone function
    from {x | x < β} to {x | x < α}. -/
def OrdinalPartitionPair (α β γ : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Bool,
    (∃ g : {x : Ordinal // x < β} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < β}, i < j → f (g i) (g j) = true) ∨
    (∃ g : {x : Ordinal // x < γ} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < γ}, i < j → f (g i) (g j) = false)

/--
Erdős Problem #1169 (Erdős and Hajnal):

Is it true that, for all finite k < ω,
  ω₁² ↛ (ω₁², k)²?

That is, for every natural number k, there exists a 2-coloring of the pairs
of ordinals below ω₁² such that no subset of order type ω₁² is monochromatic
in the first color and no subset of order type k is monochromatic in the
second color.

Hajnal proved this holds assuming the Continuum Hypothesis.
The problem is "not disprovable": open in ZFC, but true in some models.

Tags: set theory, ramsey theory
-/
theorem erdos_1169 (k : ℕ) :
    ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) :=
  sorry

end Erdos1169
