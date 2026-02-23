import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1170

/-- ω₂, the second uncountable ordinal (initial ordinal of cardinality ℵ₂). -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- The ordinal partition relation κ → (α)²₂: for every 2-coloring of increasing
    pairs of ordinals below κ, there exists a monochromatic set of order type α.
    Formalized via strictly monotone embeddings: a subset of order type α corresponds
    to a strictly monotone function from {x | x < α} to {x | x < κ}. -/
def OrdinalPartition (κ α : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < κ} → {x : Ordinal // x < κ} → Bool,
    ∃ (c : Bool) (g : {x : Ordinal // x < α} → {x : Ordinal // x < κ}),
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < α}, i < j → f (g i) (g j) = c

/--
Erdős Problem #1170:

Is it consistent that ω₂ → (α)²₂ for every α < ω₂?

The arrow notation κ → (α)²₂ denotes the ordinal partition relation: for every
2-coloring of pairs of ordinals below κ, there exists a monochromatic set of
order type α.

This is a consistency question: is there a model of ZFC in which this holds?
We formalize the property itself.

Known partial results:
- Laver [La82] proved the consistency of ω₂ → (ω₁·2+1, α)² for all α < ω₂.
- Foreman–Hajnal [FoHa03] proved the consistency of ω₂ → (ω₁²+1, α)² for all α < ω₂.

Tags: set theory, ramsey theory
-/
theorem erdos_problem_1170 :
    ∀ α : Ordinal, α < omega2 →
      OrdinalPartition omega2 α :=
  sorry

end Erdos1170
