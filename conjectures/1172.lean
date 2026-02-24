import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1172

/-!
# Erdős Problem #1172

Establish whether the following are true assuming the generalised continuum hypothesis:
  ω₃ → (ω₂, ω₁+2)²
  ω₃ → (ω₂+ω₁, ω₂+ω)²
  ω₂ → (ω₁^(ω+2)+2, ω₁+2)²

Establish whether the following is true assuming the continuum hypothesis:
  ω₂ → (ω₁+ω)²₂

A problem of Erdős and Hajnal.

Tags: set theory, ramsey theory
-/

/-- ω, the first infinite ordinal. -/
noncomputable def omega0 : Ordinal := (aleph 0).ord

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- ω₂, the second uncountable ordinal. -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- ω₃, the third uncountable ordinal. -/
noncomputable def omega3 : Ordinal := (aleph 3).ord

/-- The ordinal partition relation α → (β, γ)² for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below α, there is either
    a homogeneous set of order type β in color true, or a homogeneous set of
    order type γ in color false. Formalized via strictly monotone embeddings:
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

/-- The Generalized Continuum Hypothesis: 2^(ℵ_o) = ℵ_{o+1} for all ordinals o. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal.{0}) ^ aleph 0 = aleph 1

/--
Erdős Problem #1172, Part 1 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₃ → (ω₂, ω₁+2)²

This is an open problem of Erdős and Hajnal. The right-hand side may have
been filled in incorrectly due to a truncated photocopy of the source [Va99].
-/
theorem erdos_problem_1172a (h : GCH) :
    OrdinalPartitionPair omega3 omega2 (omega1 + 2) :=
  sorry

/--
Erdős Problem #1172, Part 2 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₃ → (ω₂+ω₁, ω₂+ω)²

This is an open problem of Erdős and Hajnal.
-/
theorem erdos_problem_1172b (h : GCH) :
    OrdinalPartitionPair omega3 (omega2 + omega1) (omega2 + omega0) :=
  sorry

/--
Erdős Problem #1172, Part 3 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₂ → (ω₁^(ω+2)+2, ω₁+2)²

This is an open problem of Erdős and Hajnal. The right-hand side may have
been filled in incorrectly due to a truncated photocopy of the source [Va99].
-/
theorem erdos_problem_1172c (h : GCH) :
    OrdinalPartitionPair omega2 (omega1 ^ (omega0 + 2) + 2) (omega1 + 2) :=
  sorry

/--
Erdős Problem #1172, Part 4 [Va99, 7.87]:

Assuming the Continuum Hypothesis, establish whether
  ω₂ → (ω₁+ω)²₂

That is, for every 2-coloring of the pairs of ordinals below ω₂, there exists
a monochromatic homogeneous set of order type ω₁+ω.

This is an open problem of Erdős and Hajnal.
-/
theorem erdos_problem_1172d (h : CH) :
    OrdinalPartitionPair omega2 (omega1 + omega0) (omega1 + omega0) :=
  sorry

end Erdos1172

end
