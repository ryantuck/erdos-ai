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

A problem of Erdős and Hajnal [Ko25b, Problem 35] [Va99, 7.88].

Status: OPEN (erdosproblems.com/1173, page last edited 25 January 2026,
accessed 2026-02-23 — "This is open, and cannot be resolved with a finite
computation."; cross-checked against the teorth/erdosproblems metadata
mirror, status last updated 2026-01-23, formalised: no).

The problem is a yes/no question; this plain-Mathlib corpus has no
`answer()` elaborator, so, following the corpus convention for open yes/no
questions, the statement below directly asserts the asked ("yes") direction
with a `sorry` proof.

Convention note: classically (Erdős–Hajnal) a *set mapping* additionally
requires α ∉ f(α), and H is then free iff f(α) ∩ H = ∅ for all α ∈ H. The
formalization drops the α ∉ f(α) requirement and correspondingly weakens
freeness to f(α) ∩ H ⊆ {α}. The two formulations are equivalent: replacing
f by g(α) = f(α) \ {α} produces a set mapping in the classical sense with
exactly the same free sets (in the respective senses), and g inherits both
cardinality hypotheses, since |g(α)| ≤ |f(α)| and g(α) ∩ g(β) ⊆ f(α) ∩ f(β).

Note that the intersection hypothesis is load-bearing: without it,
f(α) = {β | β < α} satisfies |f(α)| ≤ ℵ_ω and admits no free set with more
than one element, so the answer would trivially be "no". That f violates
|f(α) ∩ f(β)| < ℵ_ω whenever min(α, β) has cardinality ℵ_ω.

References:

[Ko25b] Problem 35. (Honest stub: the erdosproblems.com bibliography is
loaded by a separate request not captured in the session logs, and the
archived fetch of erdosproblems.com/latex/1173 carried no bibliography
block, so the expansion of the site-wide key [Ko25b] is unrecoverable
offline. Earlier pipeline guesses at the author — "Koepke, P.", "Komlós" —
are mutually contradictory and unverified, and are deliberately not
repeated as fact.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
the conference "Paul Erdős and his mathematics", Budapest, July 1999. This
problem is item 7.88. (Bibliographic stub: the expansion of the site-wide
key [Va99] was recovered from the archived fetch of
erdosproblems.com/latex/1172 — a sibling Erdős–Hajnal problem citing the
same key — since the archived fetch of /latex/1173 itself carried no
bibliography block. Not fabricated; no fuller publication data is
recoverable offline.)

The `GCH` definition is shared verbatim with the neighbouring file #1172.

No related OEIS sequences (metadata mirror: "N/A").

Tags: set theory, combinatorics
-/

/-- The Generalized Continuum Hypothesis: 2^(ℵ_α) = ℵ_{α+1} for all ordinals α. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- ω_{ω+1}, the initial ordinal of ℵ_{ω+1}. -/
noncomputable def omegaOmega1 : Ordinal := (aleph (ω + 1)).ord

/-- A set H ⊆ ω_{ω+1} is free for f if for all α ∈ H, f(α) ∩ H ⊆ {α},
    i.e., α ∉ f(β) for all distinct α, β ∈ H. (See the module docstring for
    the equivalence with the classical Erdős–Hajnal convention, which
    requires α ∉ f(α) and defines H free iff f(α) ∩ H = ∅ for all α ∈ H.) -/
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
Since H is a subset of a type of cardinality ℵ_{ω+1}, the conclusion
ℵ_{ω+1} ≤ |H| forces |H| = ℵ_{ω+1} exactly.
The cardinality comparison uses Cardinal.lift to reconcile universe levels:
subsets of {α : Ordinal // α < ω_{ω+1}} live in Type 1, while aleph lives in
Cardinal.{0}; Cardinal.lift.{1,0} embeds Cardinal.{0} into Cardinal.{1}.

This is an open yes/no question; per the corpus convention for open yes/no
questions in this plain-Mathlib corpus (no `answer()` elaborator), the
statement asserts the asked ("yes") direction directly, with a `sorry` proof.

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
