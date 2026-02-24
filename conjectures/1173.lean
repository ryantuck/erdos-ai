import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1173

/-!
# Erdős Problem #1173

Assume the generalised continuum hypothesis. Let
  f : ω_{ω+1} → [ω_{ω+1}]^{≤ ℵ_ω}
be a set mapping such that |f(α) ∩ f(β)| < ℵ_ω for all α ≠ β.
Does there exist a free set of cardinality ℵ_{ω+1}?

A problem of Erdős and Hajnal.

Tags: set theory, combinatorics
-/

/-- The Generalized Continuum Hypothesis: 2^(ℵ_α) = ℵ_{α+1} for all ordinals α. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- ω_{ω+1}, the initial ordinal of ℵ_{ω+1}. -/
noncomputable def omegaOmega1 : Ordinal := (aleph (ω + 1)).ord

/-- A set H ⊆ ω_{ω+1} is free for f if for all α ∈ H, f(α) ∩ H ⊆ {α},
    i.e., α ∉ f(β) for all distinct α, β ∈ H. -/
def IsFreeSet (f : {α : Ordinal // α < omegaOmega1} → Set {α : Ordinal // α < omegaOmega1})
    (H : Set {α : Ordinal // α < omegaOmega1}) : Prop :=
  ∀ α ∈ H, f α ∩ H ⊆ {α}

/--
Erdős Problem #1173 [Ko25b, Problem 35] [Va99, 7.88]:

Assuming the Generalised Continuum Hypothesis, let
  f : ω_{ω+1} → [ω_{ω+1}]^{≤ ℵ_ω}
be a set mapping such that |f(α) ∩ f(β)| < ℵ_ω for all α ≠ β.
Does there exist a free set of cardinality ℵ_{ω+1}?

Here ω_{ω+1} = (ℵ_{ω+1}).ord is the initial ordinal of ℵ_{ω+1}, elements are
ordinals α < ω_{ω+1}, and a free set H satisfies f(α) ∩ H ⊆ {α} for all α ∈ H.
The cardinality comparison uses Cardinal.lift to reconcile universe levels:
subsets of {α : Ordinal // α < ω_{ω+1}} live in Type 1, while aleph lives in
Cardinal.{0}; Cardinal.lift.{1,0} embeds Cardinal.{0} into Cardinal.{1}.

A problem of Erdős and Hajnal.
-/
theorem erdos_problem_1173 (h : GCH)
    (f : {α : Ordinal // α < omegaOmega1} → Set {α : Ordinal // α < omegaOmega1})
    (hf : ∀ α : {x : Ordinal // x < omegaOmega1},
      Cardinal.mk ↥(f α) ≤ Cardinal.lift.{1, 0} (aleph ω))
    (hfI : ∀ α β : {x : Ordinal // x < omegaOmega1}, α ≠ β →
      Cardinal.mk ↥(f α ∩ f β) < Cardinal.lift.{1, 0} (aleph ω)) :
    ∃ H : Set {α : Ordinal // α < omegaOmega1},
      IsFreeSet f H ∧ Cardinal.lift.{1, 0} (aleph (ω + 1)) ≤ Cardinal.mk ↥H :=
  sorry

end Erdos1173

end
